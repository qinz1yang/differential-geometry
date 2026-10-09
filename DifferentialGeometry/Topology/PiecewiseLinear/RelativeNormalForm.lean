/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArrangementGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.TwoFoldCrossing

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem simplicialMap_eqOn_convexHull_of_eqOn_vertices
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {φ ψ : E → F} (hfix : EqOn ψ φ (s : Set E)) :
    EqOn (simplicialMap K ψ) (simplicialMap K φ) (convexHull ℝ (s : Set E)) := by
  intro x hx
  rw [simplicialMap_eq_of_mem K ψ hs hx, simplicialMap_eq_of_mem K φ hs hx]
  exact Finset.sum_congr rfl fun v hv => by rw [hfix hv]

theorem doublePointSet_simplicialMap_subset_of_eqOn_subcomplex
    (K B : Geometry.SimplicialComplex ℝ E) (hBK : B.faces ⊆ K.faces)
    {φ ψ : E → F} (hfix : EqOn ψ φ B.vertices) :
    doublePointSet (simplicialMap K φ) B.space ⊆
      doublePointSet (simplicialMap K ψ) K.space := by
  have heq := simplicialMap_eqOn_subcomplex_of_eqOn_vertices K B hBK hfix
  have hspace := space_mono_of_faces_subset hBK
  rintro y ⟨a, ha, b, hb, hab, hay, hby⟩
  exact ⟨a, hspace ha, b, hspace hb, hab, (heq ha).trans hay, (heq hb).trans hby⟩

theorem mem_doublePointSet_simplicialMap_of_fixed_faces
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) {φ ψ : E → F}
    (hfix : EqOn ψ φ ((s : Set E) ∪ (t : Set E)))
    {a b : E} {y : F} (ha : a ∈ convexHull ℝ (s : Set E))
    (hb : b ∈ convexHull ℝ (t : Set E)) (hab : a ≠ b)
    (hay : simplicialMap K φ a = y) (hby : simplicialMap K φ b = y) :
    y ∈ doublePointSet (simplicialMap K ψ) K.space := by
  have heqs := simplicialMap_eqOn_convexHull_of_eqOn_vertices K hs (hfix.mono subset_union_left)
  have heqt := simplicialMap_eqOn_convexHull_of_eqOn_vertices K ht (hfix.mono subset_union_right)
  exact ⟨a, K.convexHull_subset_space hs ha, b, K.convexHull_subset_space ht hb,
    hab, (heqs ha).trans hay, (heqt hb).trans hby⟩

open Classical in
theorem exists_small_relative_vertexMap_with_coincident_edges [FiniteDimensional ℝ F]
    (φ₀ : Fin 2 → Fin 4 → F) (hind : ∀ i, AffineIndependent ℝ (φ₀ i))
    (hcommon : ∀ j ∈ ({0, 1} : Finset (Fin 4)), φ₀ 0 j = φ₀ 1 j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Fin 2 × Fin 4 → F,
      (∀ i : Fin 2, ∀ j ∈ ({0, 1} : Finset (Fin 4)), ψ (i, j) = φ₀ i j) ∧
      (∀ j ∈ ({0, 1} : Finset (Fin 4)), ψ (0, j) = ψ (1, j)) ∧
      (∀ v, dist (ψ v) (φ₀ v.1 v.2) < ε) ∧
      (∀ i : Fin 2, AffineIndependent ℝ (fun j : Fin 4 => ψ (i, j))) ∧
      ∀ s : Finset (Fin 2 × Fin 4), s.card ≤ Module.finrank ℝ F + 1 →
        AffineIndependent ℝ (fun v : (s ∩ Finset.univ.product ({0, 1} : Finset (Fin 4)) :
            Finset (Fin 2 × Fin 4)) =>
          φ₀ (v : Fin 2 × Fin 4).1 (v : Fin 2 × Fin 4).2) →
            AffineIndependent ℝ (fun v : s => ψ (v : Fin 2 × Fin 4)) := by
  let B : Finset (Fin 2 × Fin 4) := Finset.univ.product {0, 1}
  let V : Finset (Fin 2 × Fin 4) := Finset.univ \ B
  have hVB : Disjoint V B := by
    exact Finset.disjoint_left.mpr fun _ hv hb => (Finset.mem_sdiff.mp hv).2 hb
  obtain ⟨ψ, _, hfix, hclose, hgood⟩ :=
    exists_small_affineIndependent_subsets_relative V B hVB (fun v => φ₀ v.1 v.2) hε
  have hdec : (fun a b : Fin 2 × Fin 4 => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (Fin 2 × Fin 4)) := Subsingleton.elim _ _
  rw [hdec] at hgood
  have hcover : V ∪ B = Finset.univ := by ext v; simp [V]
  have hcard : 4 ≤ Module.finrank ℝ F + 1 := by
    have h := (hind 0).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (range (φ₀ 0)))) 1)
    simpa only [Fintype.card_fin] using h
  have hfixed : ∀ i : Fin 2, ∀ j ∈ ({0, 1} : Finset (Fin 4)), ψ (i, j) = φ₀ i j := by
    intro i j hj
    exact hfix (Finset.mem_product.mpr ⟨Finset.mem_univ i, hj⟩)
  refine ⟨ψ, hfixed, ?_, hclose, ?_, fun s hs hAI => ?_⟩
  · intro j hj
    exact (hfixed 0 j hj).trans ((hcommon j hj).trans (hfixed 1 j hj).symm)
  · intro i
    let I : Finset (Fin 2 × Fin 4) := ({i} : Finset (Fin 2)).product Finset.univ
    have hfst : ∀ v ∈ I, v.1 = i := by
      intro v hv
      exact Finset.mem_singleton.mp (Finset.mem_product.mp hv).1
    let e : (I ∩ B : Finset (Fin 2 × Fin 4)) ↪ Fin 4 :=
      ⟨fun v => (v : Fin 2 × Fin 4).2, fun a b hab => Subtype.ext
        (Prod.ext ((hfst _ (Finset.mem_inter.mp a.property).1).trans
          (hfst _ (Finset.mem_inter.mp b.property).1).symm) hab)⟩
    have hIB : AffineIndependent ℝ (fun v : (I ∩ B : Finset (Fin 2 × Fin 4)) =>
        φ₀ (v : Fin 2 × Fin 4).1 (v : Fin 2 × Fin 4).2) := by
      have heq : (fun v : (I ∩ B : Finset (Fin 2 × Fin 4)) =>
          φ₀ (v : Fin 2 × Fin 4).1 (v : Fin 2 × Fin 4).2) =
            fun v : (I ∩ B : Finset (Fin 2 × Fin 4)) => φ₀ i (v : Fin 2 × Fin 4).2 := by
        funext v
        rw [hfst _ (Finset.mem_inter.mp v.property).1]
      rw [heq]
      exact (hind i).comp_embedding e
    have hIcard : I.card ≤ Module.finrank ℝ F + 1 := by
      simpa [I] using hcard
    have hI : AffineIndependent ℝ (fun v : I => ψ (v : Fin 2 × Fin 4)) :=
      hgood I (by rw [hcover]; exact Finset.subset_univ I) hIcard hIB
    let eI : Fin 4 ↪ I := ⟨fun j => ⟨(i, j), by simp [I]⟩,
      fun _ _ hab => congrArg (fun v : I => (v : Fin 2 × Fin 4).2) hab⟩
    exact hI.comp_embedding eI
  · exact hgood s (by rw [hcover]; exact Finset.subset_univ s) hs hAI

open Classical in
theorem eventually_mem_space_iff_mem_coface_pair_foldedPlane [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E}
    (hs : s ∈ K.faces) (hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    {x a b : E} (hx : x ∈ openSimplex s)
    (hpair : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b}) :
    ∀ᶠ y in 𝓝 x, y ∈ K.space ↔
      y - x ∈ foldedPlane (vectorSpan ℝ (s : Set E)) (a - x) (b - x) := by
  have ha : a ∉ s ∧ insert a s ∈ K.faces := by
    change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    exact Set.mem_insert a {b}
  filter_upwards [eventually_mem_space_iff_mem_codimension_one_cone K hs hbound ⟨a, ha⟩ hx]
    with y hy
  constructor
  · intro hyK
    obtain ⟨w, hws, hwface, z, hz, r, hr, hzy⟩ := hy.mp hyK
    have hw : w = a ∨ w = b := by
      have : w ∈ {q | q ∉ s ∧ insert q s ∈ K.faces} := ⟨hws, hwface⟩
      rw [hpair] at this
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hw with rfl | rfl
    · exact Or.inl ⟨z, hz, r, hr, hzy⟩
    · exact Or.inr ⟨z, hz, r, hr, hzy⟩
  · intro hyfold
    rcases hyfold with ⟨z, hz, r, hr, hzy⟩ | ⟨z, hz, r, hr, hzy⟩
    · exact hy.mpr ⟨a, ha.1, ha.2, z, hz, r, hr, hzy⟩
    · have hb : b ∉ s ∧ insert b s ∈ K.faces := by
        change b ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
        rw [hpair]
        exact Set.mem_insert_iff.mpr (Or.inr rfl)
      exact hy.mpr ⟨b, hb.1, hb.2, z, hz, r, hr, hzy⟩

open Classical in
theorem hasPLCrossingAt_of_two_fold_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ L.faces) (hscard : s.card = 2) (htcard : t.card = 2)
    {aPos aNeg bPos bNeg x : E}
    (hKpair : {w | w ∉ s ∧ insert w s ∈ K.faces} = {aPos, aNeg})
    (hLpair : {w | w ∉ t ∧ insert w t ∈ L.faces} = {bPos, bNeg})
    (ℓ : E →ₗ[ℝ] ℝ)
    (hspan : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker ℓ)
    (haPos : 0 < ℓ (aPos - x)) (haNeg : ℓ (aNeg - x) < 0)
    (hbPos : 0 < ℓ (bPos - x)) (hbNeg : ℓ (bNeg - x) < 0)
    (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) :
    HasPLCrossingAt K.space L.space x := by
  have hSdim : Module.finrank ℝ (vectorSpan ℝ (s : Set E)) = 1 := by
    have h := (K.indep hs).finrank_vectorSpan
      (show Fintype.card s = 1 + 1 by simpa only [Fintype.card_coe] using hscard)
    have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) = 1 at h
    rwa [hrange] at h
  have hTdim : Module.finrank ℝ (vectorSpan ℝ (t : Set E)) = 1 := by
    have h := (L.indep ht).finrank_vectorSpan
      (show Fintype.card t = 1 + 1 by simpa only [Fintype.card_coe] using htcard)
    have hrange : Set.range ((↑) : t → E) = (t : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) = 1 at h
    rwa [hrange] at h
  have hKbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hscard]
    exact hK.card_le K hu
  have hLbound : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card + 1 := by
    intro u hu _
    rw [htcard]
    exact hL.card_le L hu
  exact hasPLCrossingAt_of_two_folds hdim hSdim hTdim ℓ hspan haPos haNeg hbPos hbNeg
    (eventually_mem_space_iff_mem_coface_pair_foldedPlane K hs hKbound hxs hKpair)
    (eventually_mem_space_iff_mem_coface_pair_foldedPlane L ht hLbound hxt hLpair)

open Classical in
def IsArrangementGeneralFoldPair {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ)
    (K L : Geometry.SimplicialComplex ℝ E) (s t : Finset E) (x : E) : Prop :=
  ∃ k aPos aNeg bPos bNeg,
    {w | w ∉ s ∧ insert w s ∈ K.faces} = {aPos, aNeg} ∧
      {w | w ∉ t ∧ insert w t ∈ L.faces} = {bPos, bNeg} ∧
        l k x = 0 ∧
          vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker (l k).linear ∧
            0 < l k aPos ∧ l k aNeg < 0 ∧ 0 < l k bPos ∧ l k bNeg < 0

open Classical in
theorem IsArrangementGeneralFoldPair.hasPLCrossingAt [FiniteDimensional ℝ E]
    {κ : Type*} {l : κ → E →ᵃ[ℝ] ℝ}
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ L.faces) (hscard : s.card = 2) (htcard : t.card = 2)
    {x : E} (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t)
    (h : IsArrangementGeneralFoldPair l K L s t x) :
    HasPLCrossingAt K.space L.space x := by
  obtain ⟨k, aPos, aNeg, bPos, bNeg, hKpair, hLpair, hx, hspan,
    haPos, haNeg, hbPos, hbNeg⟩ := h
  have hvsub : ∀ y : E, (l k).linear (y - x) = l k y := by
    intro y
    have hmap := (l k).linearMap_vsub y x
    simpa only [vsub_eq_sub, hx, sub_zero] using hmap
  exact hasPLCrossingAt_of_two_fold_faces K L hK hL hdim hs ht hscard htcard
    hKpair hLpair (l k).linear hspan (by rwa [hvsub]) (by rwa [hvsub])
      (by rwa [hvsub]) (by rwa [hvsub]) hxs hxt

open Classical in
theorem IsArrangementGeneralFoldPair.foldDirections_ne [FiniteDimensional ℝ E]
    {κ : Type*} {l : κ → E →ᵃ[ℝ] ℝ}
    {K L : Geometry.SimplicialComplex ℝ E} {s t : Finset E} {x : E}
    (h : IsArrangementGeneralFoldPair l K L s t x)
    (hdim : Module.finrank ℝ E = 3) (hs : s ∈ K.faces) (hscard : s.card = 2) :
    vectorSpan ℝ (s : Set E) ≠ vectorSpan ℝ (t : Set E) := by
  obtain ⟨k, aPos, _, _, _, _, _, hx, hspan, haPos, _, _, _⟩ := h
  have hlinPos : 0 < (l k).linear (aPos - x) := by
    have hmap := (l k).linearMap_vsub aPos x
    have heq : (l k).linear (aPos - x) = l k aPos := by
      simpa only [vsub_eq_sub, hx, sub_zero] using hmap
    rw [heq]
    exact haPos
  have hrange : LinearMap.range (l k).linear = ⊤ := LinearMap.range_eq_top.mpr fun c =>
    ⟨(c / (l k).linear (aPos - x)) • (aPos - x), by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hlinPos.ne']⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker (l k).linear
  have hkerdim : Module.finrank ℝ (LinearMap.ker (l k).linear) = 2 := by
    rw [hrange, finrank_top, Module.finrank_self, hdim] at hrank
    omega
  have hSdim : Module.finrank ℝ (vectorSpan ℝ (s : Set E)) = 1 := by
    have hsfin := (K.indep hs).finrank_vectorSpan
      (show Fintype.card s = 1 + 1 by simpa only [Fintype.card_coe] using hscard)
    have hrangeS : Set.range ((↑) : s → E) = (s : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) = 1 at hsfin
    rwa [hrangeS] at hsfin
  intro heq
  have hSKer : vectorSpan ℝ (s : Set E) = LinearMap.ker (l k).linear := by
    calc
      vectorSpan ℝ (s : Set E) =
          vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) := by rw [heq, sup_idem]
      _ = LinearMap.ker (l k).linear := hspan
  have hrankEq := congrArg (fun P : Submodule ℝ E => Module.finrank ℝ P) hSKer
  rw [hSdim, hkerdim] at hrankEq
  omega

open Classical in
theorem hasPLCrossingAt_of_transverse_or_arrangement_fold [FiniteDimensional ℝ E]
    {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ)
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ L.faces) {x : E}
    (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t)
    (hgeneral : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ ∨
      s.card = 2 ∧ t.card = 2 ∧ IsArrangementGeneralFoldPair l K L s t x) :
    HasPLCrossingAt K.space L.space x := by
  rcases hgeneral with htrans | ⟨hscard, htcard, hfold⟩
  · exact hasPLCrossingAt_of_transverse_face K L hK hL hdim hs ht hxs hxt htrans
  · exact hfold.hasPLCrossingAt hK hL hdim hs ht hscard htcard hxs hxt

open Classical in
def IsVertexMapGeneralInArrangement {κ ι η ζ : Type*} (l : κ → E →ᵃ[ℝ] ℝ)
    (V B : Finset ι) (φ₀ φ : ι → E) (c : η → Finset ι)
    (s t : ζ → Finset ι) : Prop :=
  (∀ v ∈ V, φ v ∈ openCell l (signVec l (φ₀ v))) ∧
    (∀ j, AffineIndependent ℝ
      (fun w : (c j ∩ (B ∪ V) : Finset ι) => φ (w : ι))) ∧
      ∀ q, Disjoint (s q) (t q) →
        (convexHull ℝ ((s q).image φ : Set E) ∩
          convexHull ℝ ((t q).image φ : Set E)).Nonempty →
            vectorSpan ℝ ((s q).image φ : Set E) ⊔
              vectorSpan ℝ ((t q).image φ : Set E) =
                (arrangementEnvelope l φ₀ (s q ∪ t q)).direction

open Classical in
theorem IsVertexMapGeneralInArrangement.layer_eq {κ ι η ζ : Type*}
    {l : κ → E →ᵃ[ℝ] ℝ} {V B : Finset ι} {φ₀ φ : ι → E}
    {c : η → Finset ι} {s t : ζ → Finset ι}
    (h : IsVertexMapGeneralInArrangement l V B φ₀ φ c s t) {v : ι} (hv : v ∈ V) :
    arrangementLayer l (φ v) = arrangementLayer l (φ₀ v) :=
  arrangementLayer_eq_of_mem_openCell l (h.1 v hv)

open Classical in
theorem IsVertexMapGeneralInArrangement.transverse {κ ι η ζ : Type*}
    {l : κ → E →ᵃ[ℝ] ℝ} {V B : Finset ι} {φ₀ φ : ι → E}
    {c : η → Finset ι} {s t : ζ → Finset ι}
    (h : IsVertexMapGeneralInArrangement l V B φ₀ φ c s t) (q : ζ)
    (hdisj : Disjoint (s q) (t q))
    (hinter : (convexHull ℝ ((s q).image φ : Set E) ∩
      convexHull ℝ ((t q).image φ : Set E)).Nonempty) :
    vectorSpan ℝ ((s q).image φ : Set E) ⊔
      vectorSpan ℝ ((t q).image φ : Set E) =
        (arrangementEnvelope l φ₀ (s q ∪ t q)).direction :=
  h.2.2 q hdisj hinter

open Classical in
theorem exists_small_vertexMap_generalInArrangement {κ ι η ζ : Type*}
    [Finite κ] [Finite η] [FiniteDimensional ℝ E]
    (l : κ → E →ᵃ[ℝ] ℝ) (V : List ι) (B : Finset ι) (hV : V.Nodup)
    (hVB : Disjoint V.toFinset B) (φ₀ : ι → E) (c : η → Finset ι)
    (s t : ζ → Finset ι)
    (hfixed : ∀ j, AffineIndependent ℝ (fun w : (c j ∩ B : Finset ι) => φ₀ (w : ι)))
    (hdim : ∀ (V₁ V₂ : List ι) (v : ι), V = V₁ ++ v :: V₂ →
      ∀ j, v ∈ c j →
        (c j ∩ (B ∪ V₂.toFinset)).card ≤
          Module.finrank ℝ (arrangementDirection l (φ₀ v)))
    (hs : ∀ q, s q ⊆ B ∪ V.toFinset) (ht : ∀ q, t q ⊆ B ∪ V.toFinset)
    (hcomplete : ∀ q (u : Finset ι), u ⊆ s q ∪ t q →
      u.card ≤ Module.finrank ℝ (arrangementEnvelope l φ₀ (s q ∪ t q)).direction + 1 →
        ∃ j, c j = u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → E, EqOn φ φ₀ ((V.toFinset : Set ι)ᶜ) ∧
      (∀ v, dist (φ v) (φ₀ v) < ε) ∧
        IsVertexMapGeneralInArrangement l V.toFinset B φ₀ φ c s t := by
  obtain ⟨φ, hfix, hclose, hcell, hgood, htrans⟩ :=
    exists_small_vertexMap_transverse_in_arrangement l V B hV hVB φ₀ c s t
      hfixed hdim hs ht hcomplete hε
  exact ⟨φ, hfix, hclose, hcell, hgood, htrans⟩

open Classical in
def IsBoundaryArrangementGeneralPair {κ : Type*} (l : κ → E →ₗ[ℝ] ℝ)
    (K L : Geometry.SimplicialComplex ℝ E) (s t : Finset E) (x : E) : Prop :=
  ∃ k a b,
    {w | w ∉ s ∧ insert w s ∈ K.faces} = {a} ∧
      {w | w ∉ t ∧ insert w t ∈ L.faces} = {b} ∧ l k x = 0 ∧
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker (l k) ∧
          0 < l k a ∧ 0 < l k b

open Classical in
theorem IsBoundaryArrangementGeneralPair.hasPLBoundaryCrossingAt [FiniteDimensional ℝ E]
    {κ : Type*} {l : κ → E →ₗ[ℝ] ℝ}
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ L.faces) (hscard : s.card = 2) (htcard : t.card = 2)
    {x : E} (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t)
    (h : IsBoundaryArrangementGeneralPair l K L s t x) :
    ∃ k, HasPLBoundaryCrossingAt {y : E | 0 ≤ l k y} K.space L.space x := by
  obtain ⟨k, a, b, hKpair, hLpair, hx, hspan, ha, hb⟩ := h
  have hKbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hscard]
    exact hK.card_le K hu
  have hLbound : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card + 1 := by
    intro u hu _
    rw [htcard]
    exact hL.card_le L hu
  exact ⟨k, hasPLBoundaryCrossingAt_of_unique_cofaces K L hdim hs ht hscard htcard
    hKbound hLbound hKpair hLpair (l k) hspan ha hb hx hxs hxt⟩

end DifferentialGeometry.Topology.PiecewiseLinear
