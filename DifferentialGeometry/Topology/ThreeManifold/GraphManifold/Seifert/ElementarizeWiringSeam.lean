import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# Synced seams between two product pieces

Lane P1W (P1 wiring), `docs/geometrization/handoffs/20261003-survey-p1-morse-decomposition.md` §2
(synchronisation) and MD6 T2 (new seams `(t, s) ↦ Φ̃ (κ s) …`).

Two product pieces `Φ_L : Q_L × S¹ → X`, `Φ_R : Q_R × S¹ → X` (smooth, injective, bijective
differential) meet along the boundary circles `l_L`, `l_R`, and a flow `φ` of `X` synchronises
both collars: `Φ_L (Q_L.collar l_L (t, s), v) = φ (-d s) (Φ_L (… (t, 0), v))` and
`Φ_R (Q_R.collar l_R (t, s), v) = φ (d s) (Φ_R (… (t, 0), v))` for `0 ≤ s < 1`. If the two side tori
`sideTorus` have the same image and the sweep `(t, s) ↦ φ (d s) (y_L t)` is injective on
`T² × (-1, 1)`, then `exists_syncedSeam` gives the seam chart: a partial diffeomorphism with that
formula, reading the left collar for `s ≤ 0` and, through a torus diffeomorphism `m` with
`y_R ∘ m = y_L`, the right collar for `s ≥ 0`, with target in the interior.

The sweep is a local diffeomorphism at every point of `T² × (-1, 1)`: near `(t, s)` it is
`φ (d a) ∘ collarDepthMap ∘ (t, a - s)` with `a = (s + 1)/2`, where `collarDepthMap` is the left
collar map read at depth `a - s ∈ (0, 1)`, a local diffeomorphism by the inverse function theorem
at the interior points of `Q_L × S¹` (`isLocalDiffeomorphAt_collarDepthMap`). The matching is
`m t = (P_R⁻¹ (φ (d/2) (y_L t))).1` for the partial diffeomorphism `P_R` of the right collar
sweep on `T² × (0, 1)`, smooth because `P_R⁻¹` is; its inverse comes from the left side.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

theorem halfSpaceOneLift_eq_halfPoint {r : ℝ} (hr : 0 ≤ r) :
    DifferentialGeometry.Topology.Manifold.halfSpaceOneLift r = halfPoint r hr :=
  (halfPoint_eq_self _ hr (max_eq_left hr).symm).symm

def torusRealSwap : (Torus × ℝ) ≃ₘ⟮signedCollarModel, ((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1)⟯
    ((Circle × ℝ) × Circle) where
  toFun y := ((y.1.1, y.2), y.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
    (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun := ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
    (contMDiff_snd.comp contMDiff_fst)

theorem torusRealSwap_apply (y : Torus × ℝ) : torusRealSwap y = ((y.1.1, y.2), y.1.2) := rfl

section Collar

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]

def collarDepthMap {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    (Φ : Q.surface.Carrier × Circle → X) (y : Torus × ℝ) : X :=
  Φ (Q.collar l (y.1.1, DifferentialGeometry.Topology.Manifold.halfSpaceOneLift y.2), y.1.2)

theorem isLocalDiffeomorphAt_collarDepthMap {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X}
    (hΦ : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) I ∞ Φ)
    (hb : ∀ q, Bijective (mfderiv ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) I Φ q))
    (t : Torus) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    IsLocalDiffeomorphAt signedCollarModel I ∞ (collarDepthMap Q l Φ) (t, r) := by
  let lift := DifferentialGeometry.Topology.Manifold.halfSpaceOneInteriorDiffeomorph
  have h1 : IsLocalDiffeomorphAt signedCollarModel (((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1)) ∞
      torusRealSwap (t, r) := torusRealSwap.isLocalDiffeomorph _
  have h2 : IsLocalDiffeomorphAt (((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1)) (circleCollarModel.prod (𝓡 1))
      ∞ (Prod.map (Prod.map id lift) id) ((t.1, r), t.2) :=
    (((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph t.1).prodMap
      (lift.isLocalDiffeomorphAt _ _ _ hr0)).prodMap
        ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph t.2)
  have hsrc : (t.1, lift r) ∈ (Q.collar l).source := by
    rw [Q.source_eq l]
    change (DifferentialGeometry.Topology.Manifold.halfSpaceOneLift r).val 0 < 1
    rw [halfSpaceOneLift_eq_halfPoint hr0.le]
    exact hr1
  have h3 : IsLocalDiffeomorphAt (circleCollarModel.prod (𝓡 1))
      ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) ∞ (Prod.map (Q.collar l) id)
      ((t.1, lift r), t.2) :=
    ((Q.collar l).isLocalDiffeomorphAt _ _ _ hsrc).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph t.2)
  have h123 := (h1.comp _ _ h2).comp _ _ h3
  have hint : ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)).IsInteriorPoint
      (Q.collar l (t.1, lift r), t.2) :=
    (h123.isInteriorPoint_iff (by simp)).mp BoundarylessManifold.isInteriorPoint
  have h4 := isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective hΦ hint (hb _)
  exact h123.comp _ _ h4

def torusReflect (a : ℝ) : (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ) where
  toFun z := (z.1, a - z.2)
  invFun z := (z.1, a - z.2)
  left_inv z := Prod.ext rfl (sub_sub_cancel a z.2)
  right_inv z := Prod.ext rfl (sub_sub_cancel a z.2)
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)

def sideTorus {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k) (Φ : Q.surface.Carrier × Circle → X)
    (t : Torus) : X :=
  Φ (Q.collar l (t.1, halfZero), t.2)

omit [IsManifold I ∞ X] in
theorem contMDiff_sideTorus {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X}
    (hΦ : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) I ∞ Φ) :
    ContMDiff torusModel I ∞ (sideTorus Q l Φ) := by
  have h0 : ContMDiff torusModel circleCollarModel ∞
      (fun t : Torus => ((t.1, halfZero) : Circle × EuclideanHalfSpace 1)) :=
    contMDiff_fst.prodMk contMDiff_const
  have h1 : ContMDiff torusModel (SurfaceModel.model Q.surface.kind) ∞
      (fun t : Torus => Q.collar l (t.1, halfZero)) := by
    refine (Q.collar l).contMDiffOn.comp_contMDiff h0 fun t => ?_
    rw [Q.source_eq l]
    change (0 : ℝ) < 1
    exact one_pos
  exact hΦ.comp (h1.prodMk contMDiff_snd)

omit [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] in
theorem injective_sideTorus {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X} (hi : Injective Φ) : Injective (sideTorus Q l Φ) := by
  intro t t' h
  have h' := hi h
  have hs : ∀ t : Torus, ((t.1, halfZero) : Circle × EuclideanHalfSpace 1) ∈ (Q.collar l).source :=
    fun t => by
      rw [Q.source_eq l]
      change (0 : ℝ) < 1
      exact one_pos
  have h1 := (Q.collar l).injOn (hs t) (hs t') (Prod.mk.inj h').1
  exact Prod.ext (Prod.mk.inj h1).1 (Prod.mk.inj h').2

omit [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] in
theorem collarDepthMap_eq {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    (Φ : Q.surface.Carrier × Circle → X) (z : Torus × ℝ) (hz : 0 ≤ z.2) :
    collarDepthMap Q l Φ z = Φ (Q.collar l (z.1.1, halfPoint z.2 hz), z.1.2) := by
  rw [collarDepthMap, halfSpaceOneLift_eq_halfPoint hz]

omit [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] in
theorem injOn_collarDepthMap {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X} (hi : Injective Φ) :
    InjOn (collarDepthMap Q l Φ) {z | 0 < z.2 ∧ z.2 < 1} := by
  intro z hz z' hz' h
  rw [collarDepthMap_eq Q l Φ z hz.1.le, collarDepthMap_eq Q l Φ z' hz'.1.le] at h
  have h' := hi h
  have hs : ∀ (t : Circle) (r : ℝ) (h0 : 0 ≤ r), r < 1 →
      (t, halfPoint r h0) ∈ (Q.collar l).source :=
    fun t r h0 h1 => by
      rw [Q.source_eq l]
      exact h1
  have h1 := (Q.collar l).injOn (hs _ _ _ hz.2) (hs _ _ _ hz'.2) (Prod.mk.inj h').1
  have h2 : z.2 = z'.2 := congrArg (fun p : Circle × EuclideanHalfSpace 1 => p.2.val 0) h1
  exact Prod.ext (Prod.ext (Prod.mk.inj h1).1 (Prod.mk.inj h').2) h2

end Collar

section Seam

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]

theorem isLocalDiffeomorphOn_flowSweep {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X}
    (hΦ : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) I ∞ Φ)
    (hb : ∀ q, Bijective (mfderiv ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) I Φ q))
    {φ : ℝ → (X ≃ₘ⟮I, I⟯ X)} (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x)) {d : ℝ}
    (hs : ∀ t v s (hs : 0 ≤ s), s < 1 →
      Φ (Q.collar l (t, halfPoint s hs), v) = φ (-(d * s)) (Φ (Q.collar l (t, halfZero), v))) :
    IsLocalDiffeomorphOn signedCollarModel I ∞
      (fun y : Torus × ℝ => φ (d * y.2) (sideTorus Q l Φ y.1)) signedCollarSource := by
  rintro ⟨y, hy1, hy2⟩
  set a : ℝ := (y.2 + 1) / 2 with ha
  have hr0 : 0 < a - y.2 := by rw [ha]; linarith
  have hr1 : a - y.2 < 1 := by rw [ha]; linarith
  have h1 : IsLocalDiffeomorphAt signedCollarModel signedCollarModel ∞ (torusReflect a) y :=
    (torusReflect a).isLocalDiffeomorph y
  have h2 := isLocalDiffeomorphAt_collarDepthMap Q l hΦ hb y.1 hr0 hr1
  have h3 : IsLocalDiffeomorphAt I I ∞ (φ (d * a)) (collarDepthMap Q l Φ (torusReflect a y)) :=
    (φ (d * a)).isLocalDiffeomorph _
  have h := (h1.comp _ _ h2).comp _ _ h3
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ h
  have hopen : IsOpen {z : Torus × ℝ | 0 < a - z.2 ∧ a - z.2 < 1} :=
    (isOpen_lt continuous_const (continuous_const.sub continuous_snd)).inter
      (isOpen_lt (continuous_const.sub continuous_snd) continuous_const)
  filter_upwards [hopen.mem_nhds ⟨hr0, hr1⟩] with z hz
  change φ (d * z.2) (sideTorus Q l Φ z.1) =
    φ (d * a) (collarDepthMap Q l Φ (z.1, a - z.2))
  rw [collarDepthMap_eq Q l Φ (z.1, a - z.2) hz.1.le]
  change φ (d * z.2) (sideTorus Q l Φ z.1) =
    φ (d * a) (Φ (Q.collar l (z.1.1, halfPoint (a - z.2) hz.1.le), z.1.2))
  rw [hs z.1.1 z.1.2 (a - z.2) hz.1.le hz.2, ← hφadd]
  congr 2
  ring

theorem isLocalDiffeomorphOn_collarFlow {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X}
    (hΦ : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) I ∞ Φ)
    (hb : ∀ q, Bijective (mfderiv ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) I Φ q))
    {φ : ℝ → (X ≃ₘ⟮I, I⟯ X)} {e : ℝ}
    (hs : ∀ t v s (hs : 0 ≤ s), s < 1 →
      Φ (Q.collar l (t, halfPoint s hs), v) = φ (e * s) (Φ (Q.collar l (t, halfZero), v))) :
    IsLocalDiffeomorphOn signedCollarModel I ∞
      (fun y : Torus × ℝ => φ (e * y.2) (sideTorus Q l Φ y.1)) {y | 0 < y.2 ∧ y.2 < 1} := by
  rintro ⟨y, hy0, hy1⟩
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
    (isLocalDiffeomorphAt_collarDepthMap Q l hΦ hb y.1 hy0 hy1)
  have hopen : IsOpen {z : Torus × ℝ | 0 < z.2 ∧ z.2 < 1} :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  filter_upwards [hopen.mem_nhds ⟨hy0, hy1⟩] with z hz
  rw [collarDepthMap_eq Q l Φ z hz.1.le, hs z.1.1 z.1.2 z.2 hz.1.le hz.2]
  rfl

omit [IsManifold I ∞ X] in
theorem injOn_collarFlow {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)
    {Φ : Q.surface.Carrier × Circle → X} (hi : Injective Φ) {φ : ℝ → (X ≃ₘ⟮I, I⟯ X)} {e : ℝ}
    (hs : ∀ t v s (hs : 0 ≤ s), s < 1 →
      Φ (Q.collar l (t, halfPoint s hs), v) = φ (e * s) (Φ (Q.collar l (t, halfZero), v))) :
    InjOn (fun y : Torus × ℝ => φ (e * y.2) (sideTorus Q l Φ y.1)) {y | 0 < y.2 ∧ y.2 < 1} := by
  intro z hz z' hz' h
  refine injOn_collarDepthMap Q l hi hz hz' ?_
  rw [collarDepthMap_eq Q l Φ z hz.1.le, collarDepthMap_eq Q l Φ z' hz'.1.le,
    hs z.1.1 z.1.2 z.2 hz.1.le hz.2, hs z'.1.1 z'.1.2 z'.2 hz'.1.le hz'.2]
  exact h

theorem exists_syncedSeam {kL kR : ℕ} (QL : PlanarBase.{u} kL) (QR : PlanarBase.{u} kR)
    (lL : Fin kL) (lR : Fin kR) {ΦL : QL.surface.Carrier × Circle → X}
    {ΦR : QR.surface.Carrier × Circle → X}
    (hΦL : ContMDiff ((SurfaceModel.model QL.surface.kind).prod (𝓡 1)) I ∞ ΦL)
    (hΦR : ContMDiff ((SurfaceModel.model QR.surface.kind).prod (𝓡 1)) I ∞ ΦR)
    (hbL : ∀ q, Bijective (mfderiv ((SurfaceModel.model QL.surface.kind).prod (𝓡 1)) I ΦL q))
    (hbR : ∀ q, Bijective (mfderiv ((SurfaceModel.model QR.surface.kind).prod (𝓡 1)) I ΦR q))
    (hiL : Injective ΦL) (hiR : Injective ΦR) {φ : ℝ → (X ≃ₘ⟮I, I⟯ X)}
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
      (injOn_collarFlow QR lR hiR hsR)
  have hsL' : ∀ t v s (hs : 0 ≤ s), s < 1 →
      ΦL (QL.collar lL (t, halfPoint s hs), v) =
        φ ((-d) * s) (ΦL (QL.collar lL (t, halfZero), v)) :=
    fun t v s hs h1 => by rw [hsL t v s hs h1, neg_mul]
  obtain ⟨PL, hPLs, hPLt, hPLf⟩ :=
    (isLocalDiffeomorphOn_collarFlow QL lL hΦL hbL hsL').exists_partialDiffeomorph_of_injOn hV
      hVne (injOn_collarFlow QL lL hiL hsL')
  have hiyL : Injective yL := injective_sideTorus QL lL hiL
  have hiyR : Injective yR := injective_sideTorus QR lR hiR
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

end GC.Seifert.Wiring
