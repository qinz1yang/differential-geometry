import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringSystem

/-!
# Piece systems with synchronised and given seams

Lane P1X2 (P1 wiring, the Möbius branch), bookkeeping part.

`exists_syncedSeam` asks the two product maps to be injective. Its proof only uses injectivity
on the half collars of the two sides, so `exists_syncedSeam_of_injOn` assumes exactly that:
`(t, s) ↦ Φ (Q.collar l (t.1, s), t.2)` is injective on `halfCollarSource`.

A `BlockData W` is a `SyncedData W` with a second family of seams, given as charts
(`gseam`, with matchings `gmatching` and sides `gside`), and with the injectivity of the
product maps replaced by the injectivity of the collar maps of the synchronised sides. This is
the shape of a piece system in which a block of pieces (the pieces of an elementary presentation
carried over along an embedding) comes with its own seams. `BlockData.toSystem` renumbers pieces,
seams (both kinds, `γ ⊕ η`) and external sides and returns the `EmbeddedPieceSystem W`;
`BlockData.toComponentRefinement` is the component refinement when the external collars are the
port collars.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

section Collar

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]

omit [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] in
theorem injOn_collar_of_injective {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X} (hi : Injective Φ) :
    InjOn (fun p : Torus × EuclideanHalfSpace 1 => Φ (Q.collar l (p.1.1, p.2), p.1.2))
      halfCollarSource := by
  intro p hp p' hp' h
  have h' := hi h
  have hs : ∀ q : Torus × EuclideanHalfSpace 1, q ∈ halfCollarSource →
      ((q.1.1, q.2) : Circle × EuclideanHalfSpace 1) ∈ (Q.collar l).source := fun q hq => by
    rw [Q.source_eq l]
    exact hq
  have h1 := (Q.collar l).injOn (hs p hp) (hs p' hp') (Prod.mk.inj h').1
  exact Prod.ext (Prod.ext (Prod.mk.inj h1).1 (Prod.mk.inj h').2) (Prod.mk.inj h1).2

omit [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] in
theorem injective_sideTorus_of_injOn {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X}
    (hi : InjOn (fun p : Torus × EuclideanHalfSpace 1 => Φ (Q.collar l (p.1.1, p.2), p.1.2))
      halfCollarSource) : Injective (sideTorus Q l Φ) := by
  intro t t' h
  have h' := hi (zero_mem_halfCollarSource t) (zero_mem_halfCollarSource t') h
  exact (Prod.mk.inj h').1

omit [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] in
theorem injOn_collarDepthMap_of_injOn {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X}
    (hi : InjOn (fun p : Torus × EuclideanHalfSpace 1 => Φ (Q.collar l (p.1.1, p.2), p.1.2))
      halfCollarSource) :
    InjOn (collarDepthMap Q l Φ) {z | 0 < z.2 ∧ z.2 < 1} := by
  intro z hz z' hz' h
  rw [collarDepthMap_eq Q l Φ z hz.1.le, collarDepthMap_eq Q l Φ z' hz'.1.le] at h
  have h' : ((z.1, halfPoint z.2 hz.1.le) : Torus × EuclideanHalfSpace 1) =
      (z'.1, halfPoint z'.2 hz'.1.le) :=
    hi (show ((z.1, halfPoint z.2 hz.1.le) : Torus × EuclideanHalfSpace 1) ∈ halfCollarSource
      from hz.2) (show ((z'.1, halfPoint z'.2 hz'.1.le) : Torus × EuclideanHalfSpace 1) ∈
        halfCollarSource from hz'.2) h
  have h2 : z.2 = z'.2 := congrArg (fun p : Torus × EuclideanHalfSpace 1 => p.2.val 0) h'
  exact Prod.ext (Prod.mk.inj h').1 h2

omit [IsManifold I ∞ X] in
theorem injOn_collarFlow_of_injOn {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X}
    (hi : InjOn (fun p : Torus × EuclideanHalfSpace 1 => Φ (Q.collar l (p.1.1, p.2), p.1.2))
      halfCollarSource) {φ : ℝ → (X ≃ₘ⟮I, I⟯ X)} {e : ℝ}
    (hs : ∀ t v s (hs : 0 ≤ s), s < 1 →
      Φ (Q.collar l (t, halfPoint s hs), v) = φ (e * s) (Φ (Q.collar l (t, halfZero), v))) :
    InjOn (fun y : Torus × ℝ => φ (e * y.2) (sideTorus Q l Φ y.1)) {y | 0 < y.2 ∧ y.2 < 1} := by
  intro z hz z' hz' h
  refine injOn_collarDepthMap_of_injOn Q l hi hz hz' ?_
  rw [collarDepthMap_eq Q l Φ z hz.1.le, collarDepthMap_eq Q l Φ z' hz'.1.le,
    hs z.1.1 z.1.2 z.2 hz.1.le hz.2, hs z'.1.1 z'.1.2 z'.2 hz'.1.le hz'.2]
  exact h

end Collar

section Seam

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]

theorem exists_syncedSeam_of_injOn {kL kR : ℕ} (QL : PlanarBase.{u} kL) (QR : PlanarBase.{u} kR)
    (lL : Fin kL) (lR : Fin kR) {ΦL : QL.surface.Carrier × Circle → X}
    {ΦR : QR.surface.Carrier × Circle → X}
    (hΦL : ContMDiff ((SurfaceModel.model QL.surface.kind).prod (𝓡 1)) I ∞ ΦL)
    (hΦR : ContMDiff ((SurfaceModel.model QR.surface.kind).prod (𝓡 1)) I ∞ ΦR)
    (hbL : ∀ q, Bijective (mfderiv ((SurfaceModel.model QL.surface.kind).prod (𝓡 1)) I ΦL q))
    (hbR : ∀ q, Bijective (mfderiv ((SurfaceModel.model QR.surface.kind).prod (𝓡 1)) I ΦR q))
    (hiL : InjOn (fun p : Torus × EuclideanHalfSpace 1 => ΦL (QL.collar lL (p.1.1, p.2), p.1.2))
      halfCollarSource)
    (hiR : InjOn (fun p : Torus × EuclideanHalfSpace 1 => ΦR (QR.collar lR (p.1.1, p.2), p.1.2))
      halfCollarSource)
    {φ : ℝ → (X ≃ₘ⟮I, I⟯ X)}
    (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x)) {d : ℝ}
    (hsL : ∀ t v s (hs : 0 ≤ s), s < 1 →
      ΦL (QL.collar lL (t, halfPoint s hs), v) = φ (-(d * s)) (ΦL (QL.collar lL (t, halfZero), v)))
    (hsR : ∀ t v s (hs : 0 ≤ s), s < 1 →
      ΦR (QR.collar lR (t, halfPoint s hs), v) = φ (d * s) (ΦR (QR.collar lR (t, halfZero), v)))
    (hrange : range (sideTorus QL lL ΦL) = range (sideTorus QR lR ΦR))
    (hinj : InjOn (fun y : Torus × ℝ => φ (d * y.2) (sideTorus QL lL ΦL y.1))
      signedCollarSource) :
    ∃ (S : PartialDiffeomorph signedCollarModel I (Torus × ℝ) X ∞)
      (m : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
      S.source = signedCollarSource ∧
      (∀ y, S y = φ (d * y.2) (sideTorus QL lL ΦL y.1)) ∧
      (∀ t s (hs : s ≤ 0), -1 < s →
        S (t, s) = ΦL (QL.collar lL (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)) ∧
      (∀ t s (hs : 0 ≤ s), s < 1 →
        S (t, s) = ΦR (QR.collar lR ((m t).1, halfPoint s hs), (m t).2)) ∧
      (∀ y ∈ S.target, I.IsInteriorPoint y) ∧
      ∀ t, sideTorus QR lR ΦR (m t) = sideTorus QL lL ΦL t := by
  set yL := sideTorus QL lL ΦL with hyL
  set yR := sideTorus QR lR ΦR with hyR
  have hsweep := isLocalDiffeomorphOn_flowSweep QL lL hΦL hbL hφadd hsL
  have hne : (signedCollarSource : Set (Torus × ℝ)).Nonempty :=
    ⟨((1 : Torus), 0), by norm_num, by norm_num⟩
  obtain ⟨S, hSs, hSt, hSf⟩ :=
    hsweep.exists_partialDiffeomorph_of_injOn isOpen_signedCollarSource' hne hinj
  have hV : IsOpen {y : Torus × ℝ | 0 < y.2 ∧ y.2 < 1} :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  have hVne : ({y : Torus × ℝ | 0 < y.2 ∧ y.2 < 1}).Nonempty :=
    ⟨((1 : Torus), 1 / 2), by norm_num, by norm_num⟩
  obtain ⟨PR, hPRs, hPRt, hPRf⟩ :=
    (isLocalDiffeomorphOn_collarFlow QR lR hΦR hbR hsR).exists_partialDiffeomorph_of_injOn hV hVne
      (injOn_collarFlow_of_injOn QR lR hiR hsR)
  have hsL' : ∀ t v s (hs : 0 ≤ s), s < 1 →
      ΦL (QL.collar lL (t, halfPoint s hs), v) =
        φ ((-d) * s) (ΦL (QL.collar lL (t, halfZero), v)) :=
    fun t v s hs h1 => by rw [hsL t v s hs h1, neg_mul]
  obtain ⟨PL, hPLs, hPLt, hPLf⟩ :=
    (isLocalDiffeomorphOn_collarFlow QL lL hΦL hbL hsL').exists_partialDiffeomorph_of_injOn hV
      hVne (injOn_collarFlow_of_injOn QL lL hiL hsL')
  have hiyL : Injective yL := injective_sideTorus_of_injOn QL lL hiL
  have hiyR : Injective yR := injective_sideTorus_of_injOn QR lR hiR
  have hhalf : ((1 : ℝ) / 2) ∈ {r : ℝ | 0 < r ∧ r < 1} := ⟨by norm_num, by norm_num⟩
  have keyR : ∀ t, ∃ t', yR t' = yL t ∧
      PR.symm (φ (d * (1 / 2)) (yL t)) = (t', 1 / 2) := by
    intro t
    obtain ⟨t', ht'⟩ : yL t ∈ range yR := hrange ▸ mem_range_self t
    refine ⟨t', ht', ?_⟩
    have hmem : (t', (1 : ℝ) / 2) ∈ PR.source := by rw [hPRs]; exact hhalf
    have hv : PR (t', 1 / 2) = φ (d * (1 / 2)) (yL t) := by
      rw [hPRf, ← ht']
    rw [← hv]
    exact PR.left_inv hmem
  have keyL : ∀ t, ∃ t', yL t' = yR t ∧
      PL.symm (φ ((-d) * (1 / 2)) (yR t)) = (t', 1 / 2) := by
    intro t
    obtain ⟨t', ht'⟩ : yR t ∈ range yL := hrange.symm ▸ mem_range_self t
    refine ⟨t', ht', ?_⟩
    have hmem : (t', (1 : ℝ) / 2) ∈ PL.source := by rw [hPLs]; exact hhalf
    have hv : PL (t', 1 / 2) = φ ((-d) * (1 / 2)) (yR t) := by
      rw [hPLf, ← ht']
    rw [← hv]
    exact PL.left_inv hmem
  let m₀ : Torus → Torus := fun t => (PR.symm (φ (d * (1 / 2)) (yL t))).1
  let m₁ : Torus → Torus := fun t => (PL.symm (φ ((-d) * (1 / 2)) (yR t))).1
  have hm₀ : ∀ t, yR (m₀ t) = yL t := by
    intro t
    obtain ⟨t', h1, h2⟩ := keyR t
    change yR (PR.symm (φ (d * (1 / 2)) (yL t))).1 = yL t
    rw [h2]
    exact h1
  have hm₁ : ∀ t, yL (m₁ t) = yR t := by
    intro t
    obtain ⟨t', h1, h2⟩ := keyL t
    change yL (PL.symm (φ ((-d) * (1 / 2)) (yR t))).1 = yR t
    rw [h2]
    exact h1
  have hsmooth : ∀ (P : PartialDiffeomorph signedCollarModel I (Torus × ℝ) X ∞) (c : ℝ)
      (y : Torus → X), ContMDiff torusModel I ∞ y →
      (∀ t, φ c (y t) ∈ P.target) →
      ContMDiff torusModel torusModel ∞ (fun t => (P.symm (φ c (y t))).1) := by
    intro P c y hy hmaps
    have hc : ContMDiff torusModel I ∞ (fun t => φ c (y t)) := (φ c).contMDiff.comp hy
    exact contMDiff_fst.comp (P.symm.contMDiffOn.comp_contMDiff hc hmaps)
  have hmapsR : ∀ t, φ (d * (1 / 2)) (yL t) ∈ PR.target := by
    intro t
    obtain ⟨t', h1, h2⟩ := keyR t
    have hmem : (t', (1 : ℝ) / 2) ∈ PR.source := by rw [hPRs]; exact hhalf
    have hv : PR (t', 1 / 2) = φ (d * (1 / 2)) (yL t) := by
      rw [hPRf, ← h1]
    rw [← hv]
    exact PR.map_source hmem
  have hmapsL : ∀ t, φ ((-d) * (1 / 2)) (yR t) ∈ PL.target := by
    intro t
    obtain ⟨t', h1, h2⟩ := keyL t
    have hmem : (t', (1 : ℝ) / 2) ∈ PL.source := by rw [hPLs]; exact hhalf
    have hv : PL (t', 1 / 2) = φ ((-d) * (1 / 2)) (yR t) := by
      rw [hPLf, ← h1]
    rw [← hv]
    exact PL.map_source hmem
  let m : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
    { toFun := m₀
      invFun := m₁
      left_inv := fun t => hiyL ((hm₁ (m₀ t)).trans (hm₀ t))
      right_inv := fun t => hiyR ((hm₀ (m₁ t)).trans (hm₁ t))
      contMDiff_toFun := hsmooth PR _ yL (contMDiff_sideTorus QL lL hΦL) hmapsR
      contMDiff_invFun := hsmooth PL _ yR (contMDiff_sideTorus QR lR hΦR) hmapsL }
  have hSapp : ∀ y, S y = φ (d * y.2) (yL y.1) := fun y => congrFun hSf y
  refine ⟨S, m, hSs, hSapp, ?_, ?_, ?_, hm₀⟩
  · intro t s hs h1
    rw [hSapp, hsL t.1 t.2 (-s) (neg_nonneg.2 hs) (by linarith)]
    congr 2
    ring
  · intro t s hs h1
    rw [hSapp, hsR (m t).1 (m t).2 s hs h1]
    change φ (d * s) (yL t) = φ (d * s) (yR (m₀ t))
    rw [hm₀]
  · intro y hy
    rw [hSt] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ((hsweep ⟨z, hz⟩).isInteriorPoint_iff (by simp)).mp
      BoundarylessManifold.isInteriorPoint

end Seam

structure BlockData (W : CompactCarrier.{u}) where
  ι : Type
  [fintypeι : Fintype ι]
  nonempty : Nonempty ι
  γ : Type
  [fintypeγ : Fintype γ]
  η : Type
  [fintypeη : Fintype η]
  ε : Type
  [fintypeε : Fintype ε]
  kind : ι → ℕ
  kind_mem : ∀ x, kind x ∈ ({1, 2, 3} : Finset ℕ)
  base : ∀ x, PlanarBase.{u} (kind x)
  map : ∀ x, (base x).surface.Carrier × Circle → W.Carrier
  smooth : ∀ x, ContMDiff ((SurfaceModel.model (base x).surface.kind).prod (𝓡 1)) W.model ∞
    (map x)
  mfderiv_bijective : ∀ x q, Bijective
    (mfderiv ((SurfaceModel.model (base x).surface.kind).prod (𝓡 1)) W.model (map x) q)
  covers : ⋃ x, range (map x) = univ
  side : γ → Bool → Σ x, Fin (kind x)
  gside : η → Bool → Σ x, Fin (kind x)
  ext : ε → Σ x, Fin (kind x)
  sides_bijective : Bijective (Sum.elim (uncurry side) (Sum.elim (uncurry gside) ext))
  collarInj : ∀ c b, InjOn (fun p : Torus × EuclideanHalfSpace 1 =>
    map (side c b).1 ((base _).collar (side c b).2 (p.1.1, p.2), p.1.2)) halfCollarSource
  flow : γ → ℝ → (W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier)
  flow_add : ∀ c s t x, flow c (s + t) x = flow c s (flow c t x)
  rate : ℝ
  sync_left : ∀ c t v s (hs : 0 ≤ s), s < 1 →
    map (side c true).1 ((base _).collar (side c true).2 (t, halfPoint s hs), v) =
      flow c (-(rate * s)) (map (side c true).1 ((base _).collar (side c true).2 (t, halfZero), v))
  sync_right : ∀ c t v s (hs : 0 ≤ s), s < 1 →
    map (side c false).1 ((base _).collar (side c false).2 (t, halfPoint s hs), v) =
      flow c (rate * s) (map (side c false).1 ((base _).collar (side c false).2 (t, halfZero), v))
  range_eq : ∀ c, range (sideTorus (base (side c true).1) (side c true).2 (map (side c true).1)) =
    range (sideTorus (base (side c false).1) (side c false).2 (map (side c false).1))
  injOn : ∀ c, InjOn (fun y : Torus × ℝ => flow c (rate * y.2)
    (sideTorus (base (side c true).1) (side c true).2 (map (side c true).1) y.1))
    signedCollarSource
  gmatching : η → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  gseam : η → PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞
  gseam_source : ∀ c, (gseam c).source = signedCollarSource
  gseam_neg : ∀ c t s (hs : s ≤ 0), -1 < s → gseam c (t, s) =
    map (gside c true).1 ((base _).collar (gside c true).2
      (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)
  gseam_pos : ∀ c t s (hs : 0 ≤ s), s < 1 → gseam c (t, s) =
    map (gside c false).1 ((base _).collar (gside c false).2
      ((gmatching c t).1, halfPoint s hs), (gmatching c t).2)
  gseam_interior : ∀ c, (gseam c).target ⊆ W.interior
  external_local : ∀ e (t : Torus), IsLocalDiffeomorphAt
    ((SurfaceModel.model (base (ext e).1).surface.kind).prod (𝓡 1)) W.model ∞
    (map (ext e).1) ((base _).collar (ext e).2 (t.1, halfZero), t.2)
  overlap : ∀ x x' q q', map x q = map x' q' →
    (⟨x, q⟩ : Σ x, (base x).surface.Carrier × Circle) = ⟨x', q'⟩ ∨
      (∃ c t, map x q = sideTorus (base (side c true).1) (side c true).2 (map (side c true).1) t) ∨
      ∃ c t, map x q = gseam c (t, 0)

namespace BlockData

attribute [instance] BlockData.fintypeι BlockData.fintypeγ BlockData.fintypeη BlockData.fintypeε

variable {W : CompactCarrier.{u}} (S : BlockData W)

open scoped Classical in
def eι : Fin (Fintype.card S.ι) ≃ S.ι := (Fintype.equivFin S.ι).symm

open scoped Classical in
def eσ : Fin (Fintype.card (S.γ ⊕ S.η)) ≃ S.γ ⊕ S.η := (Fintype.equivFin (S.γ ⊕ S.η)).symm

open scoped Classical in
def eε : Fin (Fintype.card S.ε) ≃ S.ε := (Fintype.equivFin S.ε).symm

def sideEquiv : (Σ J : Fin (Fintype.card S.ι), Fin (S.kind (S.eι J))) ≃ Σ x, Fin (S.kind x) :=
  Equiv.sigmaCongrLeft (β := fun x => Fin (S.kind x)) S.eι

theorem transport (P : ∀ x : S.ι, Fin (S.kind x) → Prop) (w : Σ x, Fin (S.kind x)) :
    P (S.eι (S.sideEquiv.symm w).1) (S.sideEquiv.symm w).2 ↔ P w.1 w.2 := by
  obtain ⟨σ, rfl⟩ := S.sideEquiv.surjective w
  rw [Equiv.symm_apply_apply]
  rfl

theorem map_collar_symm (w : Σ x, Fin (S.kind x)) (p : Circle × EuclideanHalfSpace 1)
    (v : Circle) :
    S.map (S.eι (S.sideEquiv.symm w).1) ((S.base (S.eι (S.sideEquiv.symm w).1)).collar
      (S.sideEquiv.symm w).2 p, v) = S.map w.1 ((S.base w.1).collar w.2 p, v) :=
  (S.transport (fun x l => S.map x ((S.base x).collar l p, v) =
    S.map w.1 ((S.base w.1).collar w.2 p, v)) w).mpr rfl

theorem flow_zero (c : S.γ) (x : W.Carrier) : S.flow c 0 x = x := by
  have h := S.flow_add c 0 0 x
  rw [add_zero] at h
  exact ((S.flow c 0).injective h).symm

theorem exists_seam (c : S.γ) :
    ∃ (Sm : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞)
      (m : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
      Sm.source = signedCollarSource ∧
      (∀ y, Sm y = S.flow c (S.rate * y.2)
        (sideTorus (S.base (S.side c true).1) (S.side c true).2 (S.map (S.side c true).1) y.1)) ∧
      (∀ t s (hs : s ≤ 0), -1 < s →
        Sm (t, s) = S.map (S.side c true).1 ((S.base _).collar (S.side c true).2
          (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)) ∧
      (∀ t s (hs : 0 ≤ s), s < 1 →
        Sm (t, s) = S.map (S.side c false).1 ((S.base _).collar (S.side c false).2
          ((m t).1, halfPoint s hs), (m t).2)) ∧
      (∀ y ∈ Sm.target, W.model.IsInteriorPoint y) ∧
      ∀ t, sideTorus (S.base (S.side c false).1) (S.side c false).2 (S.map (S.side c false).1)
        (m t) =
          sideTorus (S.base (S.side c true).1) (S.side c true).2 (S.map (S.side c true).1) t :=
  exists_syncedSeam_of_injOn _ _ _ _ (S.smooth _) (S.smooth _) (S.mfderiv_bijective _)
    (S.mfderiv_bijective _) (S.collarInj c true) (S.collarInj c false) (S.flow_add c)
    (S.sync_left c) (S.sync_right c) (S.range_eq c) (S.injOn c)

def seam (c : S.γ) : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
  (S.exists_seam c).choose

def matching (c : S.γ) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (S.exists_seam c).choose_spec.choose

theorem seam_spec (c : S.γ) :
    (S.seam c).source = signedCollarSource ∧
      (∀ y, S.seam c y = S.flow c (S.rate * y.2)
        (sideTorus (S.base (S.side c true).1) (S.side c true).2 (S.map (S.side c true).1) y.1)) ∧
      (∀ t s (hs : s ≤ 0), -1 < s →
        S.seam c (t, s) = S.map (S.side c true).1 ((S.base _).collar (S.side c true).2
          (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)) ∧
      (∀ t s (hs : 0 ≤ s), s < 1 →
        S.seam c (t, s) = S.map (S.side c false).1 ((S.base _).collar (S.side c false).2
          ((S.matching c t).1, halfPoint s hs), (S.matching c t).2)) ∧
      (∀ y ∈ (S.seam c).target, W.model.IsInteriorPoint y) ∧
      ∀ t, sideTorus (S.base (S.side c false).1) (S.side c false).2 (S.map (S.side c false).1)
        (S.matching c t) =
          sideTorus (S.base (S.side c true).1) (S.side c true).2 (S.map (S.side c true).1) t :=
  (S.exists_seam c).choose_spec.choose_spec

def allSide : S.γ ⊕ S.η → Bool → Σ x, Fin (S.kind x) := Sum.elim S.side S.gside

def allSeam : S.γ ⊕ S.η → PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
  Sum.elim S.seam S.gseam

def allMatching : S.γ ⊕ S.η → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :=
  Sum.elim S.matching S.gmatching

theorem allSeam_source (c : S.γ ⊕ S.η) : (S.allSeam c).source = signedCollarSource := by
  rcases c with c | c
  · exact (S.seam_spec c).1
  · exact S.gseam_source c

theorem allSeam_neg (c : S.γ ⊕ S.η) (t : Torus) (s : ℝ) (hs : s ≤ 0) (h1 : -1 < s) :
    S.allSeam c (t, s) = S.map (S.allSide c true).1 ((S.base _).collar (S.allSide c true).2
      (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2) := by
  rcases c with c | c
  · exact (S.seam_spec c).2.2.1 t s hs h1
  · exact S.gseam_neg c t s hs h1

theorem allSeam_pos (c : S.γ ⊕ S.η) (t : Torus) (s : ℝ) (hs : 0 ≤ s) (h1 : s < 1) :
    S.allSeam c (t, s) = S.map (S.allSide c false).1 ((S.base _).collar (S.allSide c false).2
      ((S.allMatching c t).1, halfPoint s hs), (S.allMatching c t).2) := by
  rcases c with c | c
  · exact (S.seam_spec c).2.2.2.1 t s hs h1
  · exact S.gseam_pos c t s hs h1

theorem allSeam_interior (c : S.γ ⊕ S.η) : (S.allSeam c).target ⊆ W.interior := by
  rcases c with c | c
  · exact fun y hy => (S.seam_spec c).2.2.2.2.1 y hy
  · exact S.gseam_interior c

theorem sides_bijective_aux :
    Bijective (Sum.elim (uncurry fun (c : Fin (Fintype.card (S.γ ⊕ S.η))) b =>
      S.sideEquiv.symm (S.allSide (S.eσ c) b)) fun e => S.sideEquiv.symm (S.ext (S.eε e))) := by
  let r : (S.γ ⊕ S.η) × Bool ⊕ S.ε ≃ S.γ × Bool ⊕ (S.η × Bool ⊕ S.ε) :=
    (Equiv.sumCongr (Equiv.sumProdDistrib S.γ S.η Bool) (Equiv.refl S.ε)).trans
      (Equiv.sumAssoc _ _ _)
  have h : (Sum.elim (uncurry fun (c : Fin (Fintype.card (S.γ ⊕ S.η))) b =>
      S.sideEquiv.symm (S.allSide (S.eσ c) b)) fun e => S.sideEquiv.symm (S.ext (S.eε e))) =
      S.sideEquiv.symm ∘ Sum.elim (uncurry S.side) (Sum.elim (uncurry S.gside) S.ext) ∘ r ∘
        (Equiv.sumCongr (Equiv.prodCongr S.eσ (Equiv.refl Bool)) S.eε) := by
    funext z
    rcases z with ⟨c, b⟩ | e
    · change S.sideEquiv.symm (S.allSide (S.eσ c) b) = S.sideEquiv.symm
        (Sum.elim (uncurry S.side) (Sum.elim (uncurry S.gside) S.ext) (r (Sum.inl (S.eσ c, b))))
      rcases S.eσ c with c' | c' <;> rfl
    · rfl
  rw [h]
  exact S.sideEquiv.symm.bijective.comp (S.sides_bijective.comp (r.bijective.comp
    (Equiv.sumCongr (Equiv.prodCongr S.eσ (Equiv.refl Bool)) S.eε).bijective))

def toSystem : EmbeddedPieceSystem W where
  count := Fintype.card S.ι
  count_pos := by
    have := S.nonempty
    exact Fintype.card_pos
  kind J := S.kind (S.eι J)
  kind_mem J := S.kind_mem _
  base J := S.base (S.eι J)
  map J := S.map (S.eι J)
  smooth J := S.smooth _
  mfderiv_bijective J := S.mfderiv_bijective _
  covers := by
    rw [← S.covers]
    exact S.eι.surjective.iUnion_comp fun x => range (S.map x)
  seamCount := Fintype.card (S.γ ⊕ S.η)
  side c b := S.sideEquiv.symm (S.allSide (S.eσ c) b)
  externalCount := Fintype.card S.ε
  externalSide e := S.sideEquiv.symm (S.ext (S.eε e))
  sides_bijective := S.sides_bijective_aux
  matching c := S.allMatching (S.eσ c)
  seam c := S.allSeam (S.eσ c)
  seam_source c := S.allSeam_source _
  seam_neg c t s hs hs1 := (S.allSeam_neg _ t s hs hs1).trans (S.map_collar_symm _ _ _).symm
  seam_pos c t s hs hs1 := (S.allSeam_pos _ t s hs hs1).trans (S.map_collar_symm _ _ _).symm
  seam_interior c := S.allSeam_interior _
  external_local e t := (S.transport (fun x l => IsLocalDiffeomorphAt
    ((SurfaceModel.model (S.base x).surface.kind).prod (𝓡 1)) W.model ∞
    (S.map x) ((S.base x).collar l (t.1, halfZero), t.2)) (S.ext (S.eε e))).mpr
      (S.external_local _ t)
  overlap J J' q q' h := by
    rcases S.overlap _ _ q q' h with h' | ⟨c, t, h'⟩ | ⟨c, t, h'⟩
    · left
      have h1 : S.eι J = S.eι J' := congrArg Sigma.fst h'
      obtain rfl : J = J' := S.eι.injective h1
      have h2 := (Sigma.mk.inj_iff.mp h').2
      rw [eq_of_heq h2]
    · right
      refine ⟨S.eσ.symm (Sum.inl c), t, ?_⟩
      rw [Equiv.apply_symm_apply]
      change _ = S.seam c (t, 0)
      rw [(S.seam_spec c).2.1, mul_zero, S.flow_zero]
      exact h'
    · right
      refine ⟨S.eσ.symm (Sum.inr c), t, ?_⟩
      rw [Equiv.apply_symm_apply]
      exact h'

theorem toSystem_externalCount : S.toSystem.externalCount = Fintype.card S.ε := rfl

theorem toSystem_external_collar (e : Fin S.toSystem.externalCount)
    (p : Circle × EuclideanHalfSpace 1) (v : Circle) :
    S.toSystem.map (S.toSystem.externalSide e).1
      ((S.toSystem.base _).collar (S.toSystem.externalSide e).2 p, v) =
        S.map (S.ext (S.eε e)).1 ((S.base _).collar (S.ext (S.eε e)).2 p, v) :=
  S.map_collar_symm _ p v

end BlockData

end GC.Seifert.Wiring

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} {T : TorusPresentation W}

def _root_.GC.Seifert.Wiring.BlockData.toComponentRefinement {i : Fin T.components.count}
    (S : GC.Seifert.Wiring.BlockData (T.Component i)) (port : S.ε ≃ T.OwnedSide i)
    (hport : ∀ e p, p ∈ halfCollarSource →
      Subtype.val (S.map (S.ext e).1 ((S.base _).collar (S.ext e).2 (p.1.1, p.2), p.1.2)) =
        T.sideCollar (port e).val p) :
    T.ComponentRefinement i where
  system := S.toSystem
  port := S.eε.trans port
  port_collar l p hp := (congrArg Subtype.val (S.toSystem_external_collar l _ _)).trans
    (hport _ p hp)

end GC.Seifert.TorusPresentation
