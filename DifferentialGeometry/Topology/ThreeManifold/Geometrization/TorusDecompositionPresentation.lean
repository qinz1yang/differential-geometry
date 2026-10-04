import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Sides
import DifferentialGeometry.Topology.Manifold.CollarFamily
import DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup

/-!
# A torus decomposition as a torus presentation

Packet B0 of the X38 survey (`handoffs/20261004-survey-b-with-tori.md` §3, review 20 §5.1–5.2).
A `TorusDecomposition M` keeps its cut carrier, components, gluing, `SmoothAssembly` and oriented
reconstruction, but its signed seams need not have pairwise disjoint targets, which a
`TorusPresentation` requires. The zero tori `torusInPrime` are compact and pairwise disjoint, so
one uniform width `δ ∈ (0, 1]` makes the shrunk seams `(t, s) ↦ primeSeam j (t, δ s)` pairwise
disjoint (`exists_disjoint_shrinkSignedCollar`, through
`Collar.disjointFamily_of_shrinking_families` applied to the seams clamped to `|s| ≤ 1/2`;
`exists_width`). With the same `δ` on both half
collars of every pairing (`TorusPairing.shrink` of `torusPairing`, whose reversal is the assembly's
`boundary_reversing`) the decomposition is a torus presentation of `NoCuts.carrier M`
(`presentationOfWidth`): same cut carrier and components, no external tori, reconstruction
`D.reconstruction`, interior chart `D.reconstruction` on the assembly's interior image, and
orientation from `quotient_oriented` followed by the oriented reconstruction.
`DecompositionPresentation D` records the identifications (cut carrier, components, seam index,
width, signed seams `primeSeam j (t, δ s)`, matchings, `cutMap = D.reconstruction ∘ quotientMap`);
`exists_decompositionPresentation` is the frozen X38 statement, all ledger fields by `rfl`.

Port bridge. For any such record the ports of every piece are π₁-injective at every basepoint
when `D` is incompressible (`DecompositionPresentation.pieceBoundaryTori_incompressible`): a port
followed by the piece-to-`M` map is the zero torus `torusInPrime j` on a left side
(`cutMap_leftCollar_zero`) and `rightTorusInPrime j = torusInPrime j ∘ matching⁻¹` on a right side
(`cutMap_rightCollar_zero`), so `injective_inner_of_composite` applies. With at least one seam,
every piece of a torus presentation of a closed connected manifold owns a side
(`TorusPresentation.nonempty_ownedSide_of_pairing_pos`; a piece without sides would have clopen
image). For the actual `D` every component carrier therefore has incompressible boundary tori
exhausting its boundary, nonempty when `0 < D.boundary.count`
(`exists_incompressible_boundaryTori`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (T : TorusPresentation (NoCuts.carrier Q))

private theorem not_mem_block_of_isEmpty {i : Fin T.components.count}
    (h : IsEmpty (T.OwnedSide i)) {x : T.cutCarrier.Carrier} (hx : x ∈ T.components.piece i)
    (j : Fin T.pairing.count) : x ∉ T.pairing.gluing.block j := by
  intro hb
  rcases hb with hb | hb
  · have he : T.leftPiece j = i := by
      by_contra hn
      exact (T.components.disjoint hn).le_bot ⟨T.left_owned j hb, hx⟩
    exact h.false ⟨.inl j, he⟩
  · have he : T.rightPiece j = i := by
      by_contra hn
      exact (T.components.disjoint hn).le_bot ⟨T.right_owned j hb, hx⟩
    exact h.false ⟨.inr (.inl j), he⟩

private theorem mem_piece_of_cutMap_eq {i : Fin T.components.count}
    (h : IsEmpty (T.OwnedSide i)) {x y : T.cutCarrier.Carrier} (hx : x ∈ T.components.piece i)
    (he : T.cutMap x = T.cutMap y) : y ∈ T.components.piece i := by
  rcases Quotient.exact (T.reconstruction.injective he) with he | ⟨j, hj, _⟩
  · exact he ▸ hx
  · exact False.elim (T.not_mem_block_of_isEmpty h hx j hj)

theorem pairing_count_eq_zero_of_isEmpty_ownedSide (i : Fin T.components.count)
    (h : IsEmpty (T.OwnedSide i)) : T.pairing.count = 0 := by
  let S : Set T.cutCarrier.Carrier := T.components.piece i
  let K := T.cutMap '' S
  have hc : Continuous T.cutMap := T.quotient_smooth.continuous
  have hsurj : Function.Surjective T.cutMap := fun y => by
    obtain ⟨x, hx⟩ := Quotient.exists_rep (T.reconstruction.symm y)
    refine ⟨x, ?_⟩
    change T.reconstruction (Quotient.mk'' x) = y
    rw [show (Quotient.mk'' x : T.pairing.QuotientSpace) = T.reconstruction.symm y from hx,
      Homeomorph.apply_symm_apply]
  have hk : IsClosed K := ((T.components.piece_compact i).image hc).isClosed
  have he : Kᶜ = T.cutMap '' Sᶜ := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, fun hx => hy ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
      exact hx (T.mem_piece_of_cutMap_eq h hz he)
  have ho : IsOpen K := by
    apply isClosed_compl_iff.mp
    rw [he]
    exact ((T.components.piece i).isOpen.isClosed_compl.isCompact.image hc).isClosed
  have hn : K.Nonempty := by
    let := T.components.connected i
    obtain ⟨x⟩ := (inferInstance : Nonempty (T.components.piece i))
    exact ⟨T.cutMap x, x, x.property, rfl⟩
  have hu : K = Set.univ := IsClopen.eq_univ ⟨hk, ho⟩ hn
  by_contra hs
  let j : Fin T.pairing.count := ⟨0, Nat.pos_of_ne_zero hs⟩
  have hm : T.cutMap (T.pairing.leftParam j 1) ∈ K := by
    rw [hu]
    trivial
  obtain ⟨z, hz, hze⟩ := hm
  exact T.not_mem_block_of_isEmpty h (T.mem_piece_of_cutMap_eq h hz hze) j
    (Or.inl (T.pairing.leftParam j 1).property)

theorem nonempty_ownedSide_of_pairing_pos (hn : 0 < T.pairing.count)
    (i : Fin T.components.count) : Nonempty (T.OwnedSide i) := by
  by_contra h
  have := T.pairing_count_eq_zero_of_isEmpty_ownedSide i (not_nonempty_iff.mp h)
  omega

theorem card_ownedSide_pos (hn : 0 < T.pairing.count) (i : Fin T.components.count) :
    0 < Fintype.card (T.OwnedSide i) := by
  have := T.nonempty_ownedSide_of_pairing_pos hn i
  exact Fintype.card_pos

end GC.Seifert.TorusPresentation

namespace GC.Topology.TorusDecomposition

private def clampHalf (s : ℝ) : ℝ := max (-(1 / 2)) (min s (1 / 2))

private theorem continuous_clampHalf : Continuous clampHalf :=
  continuous_const.max (continuous_id.min continuous_const)

private theorem clampHalf_of_abs_le {s : ℝ} (h : |s| ≤ 1 / 2) : clampHalf s = s := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [clampHalf, min_eq_left h2, max_eq_right h1]

private theorem clampHalf_mem (t : Torus) (s : ℝ) : (t, clampHalf s) ∈ signedCollarSource := by
  refine ⟨?_, ?_⟩
  · change -1 < max (-(1 / 2)) (min s (1 / 2))
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · change max (-(1 / 2)) (min s (1 / 2)) < 1
    exact max_lt (by norm_num) (lt_of_le_of_lt (min_le_right _ _) (by norm_num))

theorem exists_disjoint_shrinkSignedCollar {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type u} [TopologicalSpace N] [T2Space N] [ChartedSpace G N] {n : ℕ}
    (c : Fin n → PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞)
    (hc : ∀ i, (c i).source = signedCollarSource)
    (hdisj : Pairwise fun i j =>
      Disjoint (Set.range fun t => c i (t, 0)) (Set.range fun t => c j (t, 0))) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, δ ≤ 1 ∧ Pairwise fun i j =>
      Disjoint (shrinkSignedCollar hδ (c i)).target (shrinkSignedCollar hδ (c j)).target := by
  let f : Fin n → ULift.{u} Torus × ℝ → N := fun i p => c i (p.1.down, clampHalf p.2)
  have hf : ∀ i, Continuous (f i) := by
    intro i
    refine (c i).contMDiffOn.continuousOn.comp_continuous
      ((continuous_uliftDown.comp continuous_fst).prodMk
        (continuous_clampHalf.comp continuous_snd)) fun p => ?_
    rw [hc]
    exact clampHalf_mem _ _
  obtain ⟨δ', hδ', hδ'1, hpair⟩ := Collar.disjointFamily_of_shrinking_families
    (E := fun _ => ULift.{u} Torus × ℝ)
    (K := fun _ => (Set.univ : Set (ULift.{u} Torus)) ×ˢ Set.Icc (-1 : ℝ) 1)
    (core := fun _ => (Set.univ : Set (ULift.{u} Torus)) ×ˢ ({0} : Set ℝ))
    (c := f) (hc := hf)
    (V := fun _ δ => (Set.univ : Set (ULift.{u} Torus)) ×ˢ Set.Ioo (-δ) δ)
    (fun _ => isCompact_univ.prod isCompact_Icc)
    (fun _ δ _ hδ1 q hq => ⟨trivial,
      ⟨by linarith [neg_le_neg hδ1, hq.2.1], by linarith [hq.2.2, hδ1]⟩⟩)
    (fun _ {a b} ha hab q hq => ⟨trivial,
      ⟨by linarith [ha, hq.2.1, hab], by linarith [hq.2.2, hab]⟩⟩)
    (fun _ x hx => by
      have hzero : x.2 = 0 := by
        by_contra hne
        have hε : 0 < |x.2| / 2 := half_pos (abs_pos.mpr hne)
        have hcl := hx (|x.2| / 2) hε
        have hsub : closure ((Set.univ : Set (ULift.{u} Torus)) ×ˢ
            Set.Ioo (-(|x.2| / 2)) (|x.2| / 2)) ⊆
            {q : ULift.{u} Torus × ℝ | q.2 ∈ Set.Icc (-(|x.2| / 2)) (|x.2| / 2)} :=
          closure_minimal (fun q hq => Set.Ioo_subset_Icc_self hq.2)
            (isClosed_Icc.preimage continuous_snd)
        have hle : |x.2| ≤ |x.2| / 2 := abs_le.mpr (hsub hcl)
        have hz : |x.2| = 0 := by linarith [abs_nonneg x.2]
        exact hne (abs_eq_zero.mp hz)
      exact ⟨trivial, by simpa using hzero⟩)
    (fun i j hij => by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
      have hp0 : f i p = c i (p.1.down, 0) := by
        change c i (p.1.down, clampHalf p.2) = _
        rw [show p.2 = 0 from hp.2, clampHalf_of_abs_le (by norm_num)]
      have hq0 : f j q = c j (q.1.down, 0) := by
        change c j (q.1.down, clampHalf q.2) = _
        rw [show q.2 = 0 from hq.2, clampHalf_of_abs_le (by norm_num)]
      exact Set.disjoint_left.mp (hdisj hij) ⟨p.1.down, hp0.symm⟩
        ⟨q.1.down, hq0.symm.trans hpq⟩)
  have hδ : 0 < δ' / 2 := half_pos hδ'
  have htarget : ∀ k, (shrinkSignedCollar hδ (c k)).target ⊆
      f k '' ((Set.univ : Set (ULift.{u} Torus)) ×ˢ Set.Ioo (-δ') δ') := by
    intro k y hy
    set φ := shrinkSignedCollar hδ (c k)
    have hs := φ.map_target' hy
    rw [← φ.right_inv' hy]
    obtain ⟨h1, h2⟩ := hs.2
    have hlt : |δ' / 2 * (φ.symm y).2| < δ' / 2 := by
      rw [abs_mul, abs_of_pos hδ]
      exact mul_lt_of_lt_one_right hδ (abs_lt.mpr ⟨h1, h2⟩)
    obtain ⟨l1, l2⟩ := abs_lt.mp hlt
    refine ⟨(ULift.up (φ.symm y).1, δ' / 2 * (φ.symm y).2),
      ⟨trivial, by linarith, by linarith⟩, ?_⟩
    change c k (_, clampHalf _) = c k (_, δ' / 2 * _)
    rw [clampHalf_of_abs_le (by linarith)]
    rfl
  exact ⟨δ' / 2, hδ, by linarith, fun i j hij =>
    (hpair hij).mono (htarget i) (htarget j)⟩

private def imageOpensDiffeomorph {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (e : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (U : TopologicalSpace.Opens M) :
    U ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (⟨e '' U, e.toHomeomorph.isOpenMap _ U.isOpen⟩ : TopologicalSpace.Opens N) where
  toFun x := ⟨e x, Set.mem_image_of_mem e x.property⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨x, hx, he⟩ := y.property
    rw [← he, e.symm_apply_apply]
    exact hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp (e.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp (e.symm.contMDiff.comp contMDiff_subtype_val)

variable {M : ConnectedClosedOrientedManifold.{u} 3} (D : TorusDecomposition M)

def torusPairing : TorusPairing D.carrier where
  count := D.boundary.count
  gluing := D.boundary.gluing
  leftParam := D.boundary.leftParam
  rightParam := D.boundary.rightParam
  matching := D.boundary.matching
  matching_eq := D.boundary.matching_eq
  leftCollar := D.boundary.leftCollar
  rightCollar := D.boundary.rightCollar
  left_source := D.boundary.left_source
  right_source := D.boundary.right_source
  left_zero := D.boundary.left_zero
  right_zero := D.boundary.right_zero
  reversing := D.reconstructionAtlas.boundary_reversing

theorem exists_width : ∃ δ : ℝ, ∃ hδ : 0 < δ, δ ≤ 1 ∧ Pairwise fun i j =>
    Disjoint (shrinkSignedCollar hδ (D.reconstructionAtlas.primeSeam D.reconstruction i)).target
      (shrinkSignedCollar hδ (D.reconstructionAtlas.primeSeam D.reconstruction j)).target := by
  refine exists_disjoint_shrinkSignedCollar _
    (fun i => D.reconstructionAtlas.primeSeam_source D.reconstruction i) fun i j hij => ?_
  have h := D.reconstructionAtlas.torusInPrime_pairwise_disjoint D.reconstruction hij
  simpa only [D.reconstructionAtlas.primeSeam_zero] using h

def reconstructionHomeomorph : D.boundary.Assembled ≃ₜ M.Carrier := by
  let := D.reconstructionAtlas.charts
  exact D.reconstruction.val.toHomeomorph

theorem reconstructionHomeomorph_apply (q : D.boundary.Assembled) :
    D.reconstructionHomeomorph q = D.reconstruction.val q := rfl

def interiorImage : TopologicalSpace.Opens M.Carrier := by
  let := D.reconstructionAtlas.charts
  exact ⟨D.reconstruction.val '' (D.reconstructionAtlas.interiorImage : Set D.boundary.Assembled),
    D.reconstruction.val.toHomeomorph.isOpenMap _ D.reconstructionAtlas.interiorImage.isOpen⟩

def interiorDiffeomorph :
    D.carrier.interior ≃ₘ⟮D.carrier.model, 𝓡 3⟯ D.interiorImage := by
  let := D.reconstructionAtlas.charts
  let := D.reconstructionAtlas.smooth
  exact D.reconstructionAtlas.interiorDiffeomorph.trans
    (imageOpensDiffeomorph D.reconstruction.val D.reconstructionAtlas.interiorImage)

theorem interiorDiffeomorph_apply (x : D.carrier.interior) :
    (D.interiorDiffeomorph x).val = D.reconstruction.val (D.boundary.quotientMap x.val) := by
  change D.reconstruction.val (D.reconstructionAtlas.interiorDiffeomorph x).val = _
  rw [D.reconstructionAtlas.interior_map]

theorem quotient_oriented' (x : D.carrier.Carrier) :
    ∃ L : TangentSpace D.carrier.model x ≃ₗ[ℝ]
        TangentSpace (𝓡 3) (D.reconstructionHomeomorph (D.boundary.quotientMap x)),
      (∀ v, L v = mfderiv D.carrier.model (𝓡 3)
        (D.reconstructionHomeomorph ∘ D.boundary.quotientMap) x v) ∧
      Orientation.map (Fin 3) L (D.carrier.orientation.orientation x) =
        M.orientation.orientation (D.reconstructionHomeomorph (D.boundary.quotientMap x)) := by
  let := D.reconstructionAtlas.charts
  let := D.reconstructionAtlas.smooth
  obtain ⟨L, hL, ho⟩ := D.reconstructionAtlas.quotient_oriented x
  let q : D.carrier.Carrier → D.reconstructionAtlas.assembled.Carrier := D.boundary.quotientMap
  have hq : MDifferentiableAt D.carrier.model (𝓡 3) q x :=
    D.reconstructionAtlas.quotient_smooth.mdifferentiable (by simp) _
  let R := (D.reconstruction.val.mfderivToContinuousLinearEquiv (by simp) (q x)).toLinearEquiv
  refine ⟨L.trans R, fun v => ?_, ?_⟩
  · change mfderiv (𝓡 3) (𝓡 3) D.reconstruction.val (q x) (L v) =
      mfderiv D.carrier.model (𝓡 3) (D.reconstruction.val ∘ q) x v
    rw [mfderiv_comp x (D.reconstruction.val.mdifferentiable (by simp) _) hq, hL]
    rfl
  · have hmap : ∀ o, Orientation.map (Fin 3) (L.trans R) o =
        Orientation.map (Fin 3) R (Orientation.map (Fin 3) L o) := by
      intro o
      induction o using Module.Ray.ind with
      | h v hv => rfl
    refine (hmap _).trans ?_
    rw [ho]
    exact D.reconstruction.property (q x)

variable {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)

def presentationOfWidth (hdisj : Pairwise fun i j =>
    Disjoint (shrinkSignedCollar hδ (D.reconstructionAtlas.primeSeam D.reconstruction i)).target
      (shrinkSignedCollar hδ (D.reconstructionAtlas.primeSeam D.reconstruction j)).target) :
    TorusPresentation (NoCuts.carrier M) where
  cutCarrier := D.carrier
  components := D.components
  pairing := D.torusPairing.shrink hδ hδ1
  externalCount := 0
  external := BoundaryTori.empty _
  cutExternal := BoundaryTori.empty _
  external_exhausted := by rw [closedCarrier_boundary_eq_empty, BoundaryTori.empty_image]
  cut_boundary_exhausted := by
    rw [BoundaryTori.empty_image, Set.union_empty]
    exact D.boundary.boundary_exhausted
  external_disjoint := by
    rw [BoundaryTori.empty_image]
    exact Set.disjoint_empty _
  reconstruction := D.reconstructionHomeomorph
  quotient_smooth := by
    let := D.reconstructionAtlas.charts
    let := D.reconstructionAtlas.smooth
    exact D.reconstruction.val.contMDiff.comp D.reconstructionAtlas.quotient_smooth
  quotient_oriented := D.quotient_oriented'
  interiorImage := D.interiorImage
  interiorDiffeomorph := D.interiorDiffeomorph
  interior_map := D.interiorDiffeomorph_apply
  seam i := shrinkSignedCollar hδ (D.reconstructionAtlas.primeSeam D.reconstruction i)
  seam_source i := shrinkSignedCollar_source hδ hδ1
    (D.reconstructionAtlas.primeSeam_source D.reconstruction i)
  seam_zero i t := by
    change D.reconstructionAtlas.primeSeam D.reconstruction i (t, δ * 0) = _
    rw [mul_zero]
    exact D.reconstructionAtlas.primeSeam_zero D.reconstruction i t
  seam_positive i t s hs h1 := by
    change D.reconstruction.val (D.reconstructionAtlas.seam i (t, δ * s)) =
      D.reconstruction.val (D.boundary.quotientMap (D.boundary.rightCollar i
        (D.boundary.matching i t, halfSpaceScale hδ (halfPoint s hs))))
    rw [halfSpaceScale_halfPoint, D.reconstructionAtlas.seam_positive i t (δ * s) _ (by nlinarith)]
  seam_negative i t s hs h1 := by
    change D.reconstruction.val (D.reconstructionAtlas.seam i (t, δ * s)) =
      D.reconstruction.val (D.boundary.quotientMap (D.boundary.leftCollar i
        (t, halfSpaceScale hδ (halfPoint (-s) (neg_nonneg.mpr hs)))))
    rw [halfSpaceScale_halfPoint]
    have e : halfPoint (δ * -s) (mul_nonneg hδ.le (neg_nonneg.mpr hs)) =
        halfPoint (-(δ * s)) (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hδ.le hs)) := by
      congr 1
      ring
    rw [e, D.reconstructionAtlas.seam_negative i t (δ * s)
      (mul_nonpos_of_nonneg_of_nonpos hδ.le hs) (by nlinarith)]
  seam_interior _ _ _ := BoundarylessManifold.isInteriorPoint
  seam_disjoint := hdisj
  marked_collar i := i.elim0
  external_seam_disjoint i := i.elim0
  leftPiece := D.leftPiece
  rightPiece := D.rightPiece
  left_owned := D.left_owned
  right_owned := D.right_owned
  externalPiece i := i.elim0
  external_owned i := i.elim0

structure DecompositionPresentation {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) where
  presentation : TorusPresentation (NoCuts.carrier M)
  cut_eq : presentation.cutCarrier = D.carrier
  components_eq : cut_eq ▸ presentation.components = D.components
  seamIndex : Fin D.boundary.count ≃ Fin presentation.pairing.count
  width : ℝ
  width_pos : 0 < width
  width_le_one : width ≤ 1
  seam_eq : ∀ j p, p ∈ signedCollarSource →
    presentation.seam (seamIndex j) p =
      D.reconstructionAtlas.primeSeam D.reconstruction j (p.1, width * p.2)
  matching_eq : ∀ j, presentation.pairing.matching (seamIndex j) = D.boundary.matching j
  cutMap_eq : ∀ x : presentation.cutCarrier.Carrier,
    presentation.cutMap x = D.reconstruction.val (D.boundary.quotientMap (cut_eq ▸ x))

def decompositionPresentationOfWidth (hdisj : Pairwise fun i j =>
    Disjoint (shrinkSignedCollar hδ (D.reconstructionAtlas.primeSeam D.reconstruction i)).target
      (shrinkSignedCollar hδ (D.reconstructionAtlas.primeSeam D.reconstruction j)).target) :
    DecompositionPresentation D where
  presentation := D.presentationOfWidth hδ hδ1 hdisj
  cut_eq := rfl
  components_eq := rfl
  seamIndex := Equiv.refl _
  width := δ
  width_pos := hδ
  width_le_one := hδ1
  seam_eq _ _ _ := rfl
  matching_eq _ := rfl
  cutMap_eq _ := rfl

theorem exists_decompositionPresentation (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M) : Nonempty (DecompositionPresentation D) := by
  obtain ⟨δ, hδ, hδ1, hdisj⟩ := D.exists_width
  exact ⟨D.decompositionPresentationOfWidth hδ hδ1 hdisj⟩

namespace DecompositionPresentation

variable {M : ConnectedClosedOrientedManifold.{u} 3} {D : TorusDecomposition M}
  (P : DecompositionPresentation D)

private theorem halfZero_coord : (halfZero : EuclideanHalfSpace 1).val 0 = 0 := rfl

theorem seam_zero_eq (j : Fin D.boundary.count) (t : Torus) :
    P.presentation.seam (P.seamIndex j) (t, 0) =
      D.reconstructionAtlas.torusInPrime D.reconstruction j t := by
  rw [P.seam_eq j (t, 0) ⟨by norm_num, by norm_num⟩]
  change D.reconstructionAtlas.primeSeam D.reconstruction j (t, P.width * 0) = _
  rw [mul_zero, D.reconstructionAtlas.primeSeam_zero]

theorem cutMap_leftCollar_zero (k : Fin P.presentation.pairing.count) (t : Torus) :
    P.presentation.cutMap (P.presentation.pairing.leftCollar k (t, halfZero)) =
      D.reconstructionAtlas.torusInPrime D.reconstruction (P.seamIndex.symm k) t := by
  obtain ⟨j, rfl⟩ := P.seamIndex.surjective k
  rw [Equiv.symm_apply_apply,
    P.presentation.cutMap_leftCollar _ (zero_mem_halfCollarSource t)]
  change P.presentation.seam (P.seamIndex j) (t, -((halfZero : EuclideanHalfSpace 1).val 0)) = _
  rw [halfZero_coord, neg_zero, P.seam_zero_eq]

theorem cutMap_rightCollar_zero (k : Fin P.presentation.pairing.count) (t : Torus) :
    P.presentation.cutMap (P.presentation.pairing.rightCollar k (t, halfZero)) =
      D.reconstructionAtlas.rightTorusInPrime D.reconstruction (P.seamIndex.symm k) t := by
  obtain ⟨j, rfl⟩ := P.seamIndex.surjective k
  rw [Equiv.symm_apply_apply,
    P.presentation.cutMap_rightCollar _ (zero_mem_halfCollarSource t)]
  change P.presentation.seam (P.seamIndex j)
    ((P.presentation.pairing.matching (P.seamIndex j)).symm t,
      (halfZero : EuclideanHalfSpace 1).val 0) = _
  rw [halfZero_coord, P.matching_eq, P.seam_zero_eq,
    D.reconstructionAtlas.torusInPrime_eq_comp_matching]
  change D.reconstructionAtlas.rightTorusInPrime D.reconstruction j
    (D.boundary.matching j ((D.boundary.matching j).symm t)) = _
  rw [Diffeomorph.apply_symm_apply]

theorem pieceBoundaryTori_incompressible
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (i : Fin P.presentation.components.count) :
    (P.presentation.pieceBoundaryTori i).incompressible := by
  intro m x
  let g : C((componentCarrier P.presentation.cutCarrier P.presentation.components i).Carrier,
      M.Carrier) :=
    ⟨fun y => P.presentation.cutMap y.val,
      (P.presentation.reconstruction.continuous.comp
        P.presentation.pairing.quotientMap.continuous).comp continuous_subtype_val⟩
  apply GC.Topology.injective_inner_of_composite _ g x
  obtain ⟨f, hf, hfeq⟩ : ∃ f : C(Torus, M.Carrier),
      (∀ x, Function.Injective (FundamentalGroup.map f x)) ∧ ∀ t,
        P.presentation.cutMap (P.presentation.sideCollar
          ((Fintype.equivFin (P.presentation.OwnedSide i)).symm m).val (t, halfZero)) = f t := by
    generalize ((Fintype.equivFin (P.presentation.OwnedSide i)).symm m).val = s
    rcases s with k | k | k
    · exact ⟨_, hinj _, P.cutMap_leftCollar_zero k⟩
    · exact ⟨_, (D.reconstructionAtlas.incompressible_iff_right D.reconstruction).mp hinj _,
        P.cutMap_rightCollar_zero k⟩
    · exact (Fin.cast P.presentation.externalCount_eq_zero k).elim0
  have hcomp : g.comp ((P.presentation.pieceBoundaryTori i).boundaryMap m) = f := by
    ext t
    change P.presentation.cutMap ((P.presentation.pieceBoundaryTori i).torusMap m t).val = f t
    rw [P.presentation.pieceBoundaryTori_torusMap]
    exact hfeq t
  rw [hcomp]
  exact hf x

end DecompositionPresentation

theorem exists_incompressible_boundaryTori
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction) (i : Fin D.components.count) :
    ∃ n, ∃ B : BoundaryTori (componentCarrier D.carrier D.components i) n, B.incompressible ∧
      (componentCarrier D.carrier D.components i).model.boundary
          (componentCarrier D.carrier D.components i).Carrier = B.image ∧
      (0 < D.boundary.count → 0 < n) := by
  obtain ⟨δ, hδ, hδ1, hdisj⟩ := D.exists_width
  let P := D.decompositionPresentationOfWidth hδ hδ1 hdisj
  exact ⟨_, P.presentation.pieceBoundaryTori i, P.pieceBoundaryTori_incompressible hinj i,
    P.presentation.pieceBoundaryTori_image i, fun hpos =>
      P.presentation.card_ownedSide_pos hpos i⟩

end GC.Topology.TorusDecomposition
