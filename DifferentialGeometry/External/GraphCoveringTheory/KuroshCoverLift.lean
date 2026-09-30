/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverConnected
import DifferentialGeometry.External.GraphCoveringTheory.KuroshFreePart

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

theorem test_coverSymmCovering {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    (coverPrefunctor G H).symmetrify.IsCovering :=
  (test_coverPrefunctor_isCovering G H).symmetrify

noncomputable def test_coverStarEquiv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H) :
    @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u ≃
      @Quiver.Star (Quiver.Symmetrify (RawBassSerreVertex G))
        (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
          (rawBassSerreQuiver G))
        ((coverPrefunctor G H).symmetrify.obj u) :=
  Equiv.ofBijective ((coverPrefunctor G H).symmetrify.star u)
    ((test_coverSymmCovering G H).star_bijective u)

noncomputable def test_coverStarLift {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H) {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v) :
    @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u :=
  (test_coverStarEquiv G H u).symm ⟨v, e⟩

theorem test_coverStarLift_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H) {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v) :
    ∃ h : (coverPrefunctor G H).symmetrify.obj
        (test_coverStarLift G H u e).1 = v,
      Quiver.Hom.cast rfl h
        ((coverPrefunctor G H).symmetrify.map
          (test_coverStarLift G H u e).2) = e := by
  have h := (test_coverStarEquiv G H u).apply_symm_apply
    (⟨v, e⟩ : Quiver.Star
      ((coverPrefunctor G H).symmetrify.obj u))
  refine ⟨congrArg Sigma.fst h, ?_⟩
  rw [Quiver.Hom.cast_eq_iff_heq]
  exact (Sigma.ext_iff.mp h).2

theorem test_coverStar_eq_mk_of_map_cast {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H)
    (s : @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u)
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v)
    (hobj : (coverPrefunctor G H).symmetrify.obj s.1 = v)
    (hmap : Quiver.Hom.cast rfl hobj
      ((coverPrefunctor G H).symmetrify.map s.2) = e) :
    (coverPrefunctor G H).symmetrify.star u s = ⟨v, e⟩ := by
  apply Sigma.ext_iff.mpr
  refine ⟨hobj, ?_⟩
  rw [Quiver.Hom.cast_eq_iff_heq] at hmap
  exact hmap

theorem test_hom_reverse_cast {U : Type u} [q : Quiver.{v} U]
    [Quiver.HasReverse U] {a b a' b' : U}
    (e : a ⟶ b) (ha : a = a') (hb : b = b') :
    Quiver.reverse (e.cast ha hb) = (Quiver.reverse e).cast hb ha := by
  cases ha
  cases hb
  rfl

theorem test_coverReverseStar_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H)
    (d : @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u)
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v)
    (hobj : (coverPrefunctor G H).symmetrify.obj d.1 = v)
    (hmap : Quiver.Hom.cast rfl hobj
      ((coverPrefunctor G H).symmetrify.map d.2) = e) :
    (coverPrefunctor G H).symmetrify.map (Quiver.reverse d.2) =
      (Quiver.reverse e).cast hobj.symm rfl := by
  cases hobj
  rw [← hmap]
  simp only [Quiver.Hom.cast_rfl_rfl, Prefunctor.map_reverse]

theorem test_coverReverseStar_map_transport {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H)
    (d : @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u)
    {v w : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : v ⟶ w)
    (hobj : (coverPrefunctor G H).symmetrify.obj u = v)
    (htarget : (coverPrefunctor G H).symmetrify.obj d.1 = w)
    (hmap : Quiver.Hom.cast rfl htarget
      ((coverPrefunctor G H).symmetrify.map d.2) =
      e.cast hobj.symm rfl) :
    Quiver.Hom.cast rfl hobj
        ((coverPrefunctor G H).symmetrify.map (Quiver.reverse d.2)) =
      (Quiver.reverse e).cast htarget.symm rfl := by
  cases hobj
  cases htarget
  have hmap' :
      (coverPrefunctor G H).symmetrify.map d.2 = e := by
    simpa using hmap
  have hreverse := congrArg Quiver.reverse hmap'
  rw [Quiver.Hom.cast_rfl_rfl, Quiver.Hom.cast_rfl_rfl]
  rw [Prefunctor.map_reverse]
  exact hreverse

structure TestCoverPathLiftData {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v : Quiver.Symmetrify (RawBassSerreVertex G)} where
  x : CoverVertex G H
  path : @Quiver.Path (Quiver.Symmetrify (CoverVertex G H))
    (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H))
    (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) x
  endpoint : (coverPrefunctor G H).symmetrify.obj x = v

noncomputable def test_coverPathLiftData {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∀ {v : Quiver.Symmetrify (RawBassSerreVertex G)},
      @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
        (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
          (rawBassSerreQuiver G))
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v →
      TestCoverPathLiftData G H (v := v)
  | _, Quiver.Path.nil =>
      ⟨coverVertexMk G H (rawBassSerreOrbitRoot G H) 1,
        Quiver.Path.nil, rfl⟩
  | _, @Quiver.Path.cons _ _ _ b c p e => by
      let ih := test_coverPathLiftData G H p
      let e' := Quiver.Hom.cast ih.endpoint.symm rfl e
      let d := test_coverStarLift G H ih.x e'
      let hd := test_coverStarLift_map G H ih.x e'
      exact ⟨d.1, ih.path.cons d.2, hd.1⟩

theorem test_path_cast_cons_mid {U : Type u} [q : Quiver.{v} U]
    {a b c b' c' : U} (p : Quiver.Path a b) (e : b ⟶ c)
    (hb : b = b') (hc : c = c') :
    (p.cons e).cast rfl hc =
      (p.cast rfl hb).cons (e.cast hb hc) := by
  cases hb
  exact Quiver.Path.cast_cons p e rfl hc

theorem test_coverPathLiftData_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v) :
    ((coverPrefunctor G H).symmetrify.mapPath
        (test_coverPathLiftData G H p).path).cast rfl
        (test_coverPathLiftData G H p).endpoint = p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      let ihd := test_coverPathLiftData G H p
      let e' := Quiver.Hom.cast ihd.endpoint.symm rfl e
      let d := test_coverStarLift G H ihd.x e'
      let hd := test_coverStarLift_map G H ihd.x e'
      rcases hd with ⟨hdobj, hdmap⟩
      dsimp [test_coverPathLiftData]
      rw [test_path_cast_cons_mid
        (p := (coverPrefunctor G H).symmetrify.mapPath ihd.path)
        (e := (coverPrefunctor G H).symmetrify.map d.2)
        (hb := ihd.endpoint) (hc := hdobj)]
      rw [ih]
      have hedge :
          Quiver.Hom.cast ihd.endpoint hdobj
              ((coverPrefunctor G H).symmetrify.map d.2) = e := by
        calc
          Quiver.Hom.cast ihd.endpoint hdobj
                ((coverPrefunctor G H).symmetrify.map d.2) =
              (Quiver.Hom.cast rfl hdobj
                ((coverPrefunctor G H).symmetrify.map d.2)).cast
                ihd.endpoint rfl := by
              rw [Quiver.Hom.cast_cast]
          _ = e'.cast ihd.endpoint rfl := by rw [hdmap]
          _ = e := by
              dsimp [e']
              rw [Quiver.Hom.cast_cast]
              simp
      rw [hedge]

theorem test_coverPathLiftData_backtrack_endpoint {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v w : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v)
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) v w) :
    (test_coverPathLiftData G H
      ((p.cons e).cons (Quiver.reverse e))).x =
      (test_coverPathLiftData G H p).x := by
  let ihd := test_coverPathLiftData G H p
  let e' := Quiver.Hom.cast ihd.endpoint.symm rfl e
  let d := test_coverStarLift G H ihd.x e'
  let hd := test_coverStarLift_map G H ihd.x e'
  rcases hd with ⟨hdobj, hdmap⟩
  dsimp [test_coverPathLiftData]
  let e2 := (Quiver.reverse e).cast hdobj.symm rfl
  have hrevmap :
      Quiver.Hom.cast rfl ihd.endpoint
          ((coverPrefunctor G H).symmetrify.map (Quiver.reverse d.2)) = e2 := by
    have h := test_coverReverseStar_map_transport (G := G) (H := H)
      (u := ihd.x) (d := d) (e := e) ihd.endpoint hdobj (by
        simpa [d, e'] using hdmap)
    simpa [e2] using h
  have hstar :
      (coverPrefunctor G H).symmetrify.star d.1
          (⟨ihd.x, Quiver.reverse d.2⟩ : Quiver.Star d.1) =
        ⟨v, e2⟩ := by
    apply test_coverStar_eq_mk_of_map_cast (G := G) (H := H)
      (u := d.1) (s := ⟨ihd.x, Quiver.reverse d.2⟩) (e := e2)
      ihd.endpoint
    exact hrevmap
  have hlift :
      test_coverStarLift G H d.1 e2 =
        (⟨ihd.x, Quiver.reverse d.2⟩ : Quiver.Star d.1) := by
    apply (test_coverStarEquiv G H d.1).injective
    calc
      test_coverStarEquiv G H d.1 (test_coverStarLift G H d.1 e2) =
          ⟨v, e2⟩ := (test_coverStarEquiv G H d.1).apply_symm_apply _
      _ = test_coverStarEquiv G H d.1
          (⟨ihd.x, Quiver.reverse d.2⟩ : Quiver.Star d.1) := hstar.symm
  change
      (test_coverStarLift G H d.1 e2).1 =
        (ihd.x : Quiver.Symmetrify (CoverVertex G H))
  exact congrArg Sigma.fst hlift

theorem test_coverStarLift_fst_eq_of_heq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u u' : CoverVertex G H)
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v)
    (e' : (coverPrefunctor G H).symmetrify.obj u' ⟶ v)
    (hu : HEq u u') (he : HEq e e') :
    (test_coverStarLift G H u e).1 =
      (test_coverStarLift G H u' e').1 := by
  cases hu
  cases he
  rfl

theorem test_coverPathLiftData_append_edge_endpoint {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v w : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p q : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v)
    (h : (test_coverPathLiftData G H p).x =
      (test_coverPathLiftData G H q).x)
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) v w) :
    (test_coverPathLiftData G H (p.cons e)).x =
      (test_coverPathLiftData G H (q.cons e)).x := by
  let dp := test_coverPathLiftData G H p
  let dq := test_coverPathLiftData G H q
  let ep := Quiver.Hom.cast dp.endpoint.symm rfl e
  let eq := Quiver.Hom.cast dq.endpoint.symm rfl e
  have he_cast :
      Quiver.Hom.cast
          (congrArg (fun z : CoverVertex G H =>
            (coverPrefunctor G H).symmetrify.obj z) h) rfl ep = eq := by
    dsimp [ep, eq]
    rw [Quiver.Hom.cast_cast]
  have he : HEq ep eq :=
    (Quiver.Hom.cast_eq_iff_heq
      (congrArg (fun z : CoverVertex G H =>
        (coverPrefunctor G H).symmetrify.obj z) h) rfl ep eq).mp he_cast
  have hout := test_coverStarLift_fst_eq_of_heq G H dp.x dq.x ep eq
    (heq_of_eq h) he
  change
      (test_coverStarLift G H dp.x ep).1 =
        (test_coverStarLift G H dq.x eq).1
  exact hout

theorem test_coverPathLiftData_append_endpoint {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v w : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p q : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v)
    (h : (test_coverPathLiftData G H p).x =
      (test_coverPathLiftData G H q).x)
    (r : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) v w) :
    (test_coverPathLiftData G H (p.comp r)).x =
      (test_coverPathLiftData G H (q.comp r)).x := by
  induction r with
  | nil => simpa using h
  | @cons b c r e ih =>
      rw [Quiver.Path.comp_cons, Quiver.Path.comp_cons]
      exact test_coverPathLiftData_append_edge_endpoint G H
        (p.comp r) (q.comp r) ih e

/- theorem test_coverStarLift_eq_of_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H) {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    {e f : (coverPrefunctor G H).symmetrify.obj u ⟶ v}
    (h : test_coverStarLift G H u e = test_coverStarLift G H u f) :
    e = f := by
  have h' := congrArg
    (fun z => (test_coverStarEquiv G H u) z) h
  simpa [test_coverStarLift] using congrArg
    (fun z : @Quiver.Star (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj u) => z.2) h' -/

end GraphCoveringTheory.Kurosh
