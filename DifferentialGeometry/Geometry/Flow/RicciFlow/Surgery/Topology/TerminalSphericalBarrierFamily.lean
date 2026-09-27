import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrierCover

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

set_option backward.isDefEq.respectTransparency false in
private theorem boundary_pair_of_neck_or_cap
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {δ : ℝ} {v : M}
    (K : CompactDomain M) (nk : SpatialNeck g δ v)
    (hgeom : (K.carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, -3)) ∪
          range (fun q : Sphere 2 => nk.map (q, 3)) ∧
        Disjoint (range (fun q : Sphere 2 => nk.map (q, -3)))
          (range (fun q : Sphere 2 => nk.map (q, 3))) ∧
        (∀ b ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, b))) ∧
        ∃ (cneg : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, -3)))
          (cpos : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 3))),
          cneg.radius < 1 ∧ cpos.radius < 1 ∧
          (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
            (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
          (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
            (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) ∨
      (frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
        ∃ c : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 1 / 2)),
          c.radius < 1 / 4 ∧ ∀ q,
            c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
              (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) :
    ∃ (level sign : Fin 2 → ℝ)
      (collar : ∀ j, SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, level j))),
      frontier K.carrier = ⋃ j, range (fun q : Sphere 2 => nk.map (q, level j)) ∧
      ∀ j, |level j| ≤ 3 ∧ (sign j = 1 ∨ sign j = -1) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, level j)) ∧
        (collar j).radius < 1 ∧ ∀ q,
          (collar j).toFun q = nk.map (q.1, level j + sign j * (q.2 : ℝ)) ∧
            ((collar j).toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  rcases hgeom with ⟨_, hf, _, hs, cm, cp, hcm, hcp, hm, hp⟩ | ⟨hf, hs, c, hc, hm⟩
  · let level : Fin 2 → ℝ := ![-3, 3]
    let sign : Fin 2 → ℝ := ![-1, 1]
    let collar : ∀ j, SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, level j)) :=
      fun j => Fin.cases cm (fun j => Fin.cases cp (fun k => Fin.elim0 k) j) j
    refine ⟨level, sign, collar, ?_, ?_⟩
    · rw [hf]
      ext x
      constructor
      · rintro (hx | hx)
        · exact mem_iUnion.mpr ⟨0, hx⟩
        · exact mem_iUnion.mpr ⟨1, hx⟩
      · intro hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        fin_cases j
        · exact Or.inl hj
        · exact Or.inr hj
    · intro j
      fin_cases j
      · refine ⟨by norm_num [level], Or.inr rfl, hs (-3) (by simp), hcm, ?_⟩
        intro q
        exact ⟨by simpa [collar, level, sign, sub_eq_add_neg] using (hm q).1, (hm q).2⟩
      · refine ⟨by norm_num [level], Or.inl rfl, hs 3 (by simp), hcp, ?_⟩
        intro q
        exact ⟨by change cp.toFun q = nk.map (q.1, 3 + 1 * (q.2 : ℝ)); simpa only [one_mul] using (hp q).1, (hp q).2⟩
  · refine ⟨fun _ => 1 / 2, fun _ => 1, fun _ => c, ?_, ?_⟩
    · simpa only [iUnion_const] using hf
    · intro j
      exact ⟨by norm_num, Or.inl rfl, hs, by linarith, fun q =>
        ⟨by simpa only [one_mul] using (hm q).1, (hm q).2⟩⟩

theorem TerminalLimitMetric.exists_finite_recorded_spherical_barriers_of_canonical
    (L : G.TerminalLimitMetric) {δ C1 C2 q : ℝ}
    (hδsmall : δ < 1 / 20000)
    (hcanonical : ∀ (x : P.Carrier) (t : ℝ), t ∈ Ioo a s → q < G.flow.scalar t x →
      ∃ W : CanonicalWitness G.flow (δ / 4) C1 C2 x t, W.capTubeHasNeckChart (δ / 4))
    (A : ℝ) (y : G.terminalRegularOpen) (hA : 0 < A) (hqA : q < 4 * C2 * A)
    (hyA : metricScalarAt L.metric y ≤ A) (hnoncompact : ¬ IsCompact (connectedComponent y)) :
    ∃ (s : Finset {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
      (K : {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
          CompactDomain G.terminalRegularOpen),
      s.Nonempty ∧
      {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
        ⋃ p ∈ s, interior (K p).carrier ∧
      (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
        ∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
          metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
      ∃ (v : {p // p ∈ s} → G.terminalRegularOpen)
        (neck : ∀ p, SpatialNeck L.metric δ (v p))
        (level sign : {p // p ∈ s} × Fin 2 → ℝ)
        (collar : ∀ i, SmoothTwoSidedCollar I2 I3
          (fun z : Sphere 2 => (neck i.1).map (z, level i))),
        (∀ p, frontier (K p.val).carrier =
          ⋃ j : Fin 2, range (fun z : Sphere 2 => (neck p).map (z, level (p, j)))) ∧
        (⋃ p ∈ s, frontier (K p).carrier) =
          ⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
        (∀ p, A < (1 - 4323 * δ) * metricScalarAt L.metric (v p) ∧
          (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
            2 * A < metricScalarAt L.metric ((neck p).map z) ∧
              metricScalarAt L.metric ((neck p).map z) ≤ 8 * C2 ^ 2 * A) ∧
          (neck p).cylindricalChart.metricCloseOn L.metric δ
            {z : (neck p).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
          ∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck p).cylindricalChart.domain) ∧
        (∀ i, |level i| ≤ 3 ∧ (sign i = 1 ∨ sign i = -1) ∧
          IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
          (collar i).radius < 1 ∧ ∀ z,
            (collar i).toFun z = (neck i.1).map (z.1, level i + sign i * (z.2 : ℝ)) ∧
              ((collar i).toFun z ∈ (K i.1.val).carrier ↔ (z.2 : ℝ) ≤ 0)) ∧
        IsCompact (⋃ i : {p // p ∈ s} × Fin 2,
          range (fun z : Sphere 2 => (neck i.1).map (z, level i))) ∧
        Disjoint {z : G.terminalRegularOpen | metricScalarAt L.metric z ≤ A}
          (⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i))) := by
  classical
  obtain ⟨s, K, hs, hcov, hK, hcompact, hlow⟩ :=
    L.exists_finite_spherical_barrier_cover_of_canonical hδsmall hcanonical
      A y hA hqA hyA hnoncompact
  have hpack (p : {p // p ∈ s}) := (hK p.val p.property).2.2.2
  choose v neck hfull hmetric hdomain hgeometry using hpack
  choose level sign collar hfront hcollar using fun p =>
    boundary_pair_of_neck_or_cap (K p.val) (neck p) (hgeometry p)
  let lev : {p // p ∈ s} × Fin 2 → ℝ := fun i => level i.1 i.2
  let sgn : {p // p ∈ s} × Fin 2 → ℝ := fun i => sign i.1 i.2
  let col : ∀ i : {p // p ∈ s} × Fin 2,
      SmoothTwoSidedCollar I2 I3 (fun z : Sphere 2 => (neck i.1).map (z, lev i)) :=
    fun i => collar i.1 i.2
  have hunion : (⋃ p ∈ s, frontier (K p).carrier) =
      ⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, lev i)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hz
      have hzp' : z ∈ ⋃ j : Fin 2,
          range (fun z : Sphere 2 => (neck ⟨p, hp⟩).map (z, level ⟨p, hp⟩ j)) :=
        (hfront ⟨p, hp⟩).subset hzp
      obtain ⟨j, hj⟩ := mem_iUnion.mp hzp'
      exact mem_iUnion.mpr ⟨(⟨p, hp⟩, j), hj⟩
    · intro hz
      obtain ⟨⟨p, j⟩, hj⟩ := mem_iUnion.mp hz
      exact mem_iUnion₂.mpr ⟨p.val, p.property, (hfront p).symm.subset (mem_iUnion.mpr ⟨j, hj⟩)⟩
  refine ⟨s, K, hs, hcov, ?_, v, neck, lev, sgn, col, hfront, hunion, ?_,
    fun i => hcollar i.1 i.2, hunion ▸ hcompact, hunion ▸ hlow⟩
  · intro p hp
    exact ⟨(hK p hp).1, (hK p hp).2.1, (hK p hp).2.2.1⟩
  · intro p
    have hcenter := (hfull p ((neck p).center, 0) ⟨mem_univ _, by norm_num⟩).1
    rw [(neck p).center_eq] at hcenter
    refine ⟨?_, hfull p, hmetric p, hdomain p⟩
    nlinarith [(neck p).Q_pos]

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_finite_recorded_spherical_barriers
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000) :
    ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
      ∀ (L : G.TerminalLimitMetric) (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
        metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
        ∃ (s : Finset {z : G.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
          (K : {z : G.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
              CompactDomain G.terminalRegularOpen),
          s.Nonempty ∧
          {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
            ⋃ p ∈ s, interior (K p).carrier ∧
          (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
            ∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
              metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
          ∃ (v : {p // p ∈ s} → G.terminalRegularOpen)
            (neck : ∀ p, SpatialNeck L.metric δ (v p))
            (level sign : {p // p ∈ s} × Fin 2 → ℝ)
            (collar : ∀ i, SmoothTwoSidedCollar I2 I3
              (fun z : Sphere 2 => (neck i.1).map (z, level i))),
            (∀ p, frontier (K p.val).carrier =
              ⋃ j : Fin 2, range (fun z : Sphere 2 => (neck p).map (z, level (p, j)))) ∧
            (⋃ p ∈ s, frontier (K p).carrier) =
              ⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
            (∀ p, A < (1 - 4323 * δ) * metricScalarAt L.metric (v p) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * A < metricScalarAt L.metric ((neck p).map z) ∧
                  metricScalarAt L.metric ((neck p).map z) ≤ 8 * C2 ^ 2 * A) ∧
              (neck p).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck p).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              ∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck p).cylindricalChart.domain) ∧
            (∀ i, |level i| ≤ 3 ∧ (sign i = 1 ∨ sign i = -1) ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
              (collar i).radius < 1 ∧ ∀ z,
                (collar i).toFun z = (neck i.1).map (z.1, level i + sign i * (z.2 : ℝ)) ∧
                  ((collar i).toFun z ∈ (K i.1.val).carrier ↔ (z.2 : ℝ) ≤ 0)) ∧
            IsCompact (⋃ i : {p // p ∈ s} × Fin 2,
              range (fun z : Sphere 2 => (neck i.1).map (z, level i))) ∧
            Disjoint {z : G.terminalRegularOpen | metricScalarAt L.metric z ≤ A}
              (⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i))) := by
  obtain ⟨C2, hC2, hcoverage⟩ :=
    exists_uniform_canonical_constants_with_cap_neck_charts.{u}
      (by positivity : 0 < δ / 4) (by linarith : δ / 4 < 1 / 11)
  refine ⟨C2, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hcoverage P a s G
  refine ⟨q, hq, ?_⟩
  intro L A y hA hqA hyA hnoncompact
  exact L.exists_finite_recorded_spherical_barriers_of_canonical hδsmall
    (fun x t ht hx => hcanonical x t ⟨ht.1.le, ht.2⟩ hx.le)
    A y hA hqA hyA hnoncompact

theorem TerminalLimitMetric.exists_finite_recorded_spherical_barriers
    (L : G.TerminalLimitMetric) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000) :
    ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
      ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
        metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
        ∃ (s : Finset {z : G.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
          (K : {z : G.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
              CompactDomain G.terminalRegularOpen),
          s.Nonempty ∧
          {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
            ⋃ p ∈ s, interior (K p).carrier ∧
          (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
            ∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
              metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
          ∃ (v : {p // p ∈ s} → G.terminalRegularOpen)
            (neck : ∀ p, SpatialNeck L.metric δ (v p))
            (level sign : {p // p ∈ s} × Fin 2 → ℝ)
            (collar : ∀ i, SmoothTwoSidedCollar I2 I3
              (fun z : Sphere 2 => (neck i.1).map (z, level i))),
            (∀ p, frontier (K p.val).carrier =
              ⋃ j : Fin 2, range (fun z : Sphere 2 => (neck p).map (z, level (p, j)))) ∧
            (⋃ p ∈ s, frontier (K p).carrier) =
              ⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
            (∀ p, A < (1 - 4323 * δ) * metricScalarAt L.metric (v p) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * A < metricScalarAt L.metric ((neck p).map z) ∧
                  metricScalarAt L.metric ((neck p).map z) ≤ 8 * C2 ^ 2 * A) ∧
              (neck p).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck p).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              ∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck p).cylindricalChart.domain) ∧
            (∀ i, |level i| ≤ 3 ∧ (sign i = 1 ∨ sign i = -1) ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
              (collar i).radius < 1 ∧ ∀ z,
                (collar i).toFun z = (neck i.1).map (z.1, level i + sign i * (z.2 : ℝ)) ∧
                  ((collar i).toFun z ∈ (K i.1.val).carrier ↔ (z.2 : ℝ) ≤ 0)) ∧
            IsCompact (⋃ i : {p // p ∈ s} × Fin 2,
              range (fun z : Sphere 2 => (neck i.1).map (z, level i))) ∧
            Disjoint {z : G.terminalRegularOpen | metricScalarAt L.metric z ≤ A}
              (⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i))) := by
  obtain ⟨C2, hC2, hmain⟩ := exists_uniform_finite_recorded_spherical_barriers.{u} hδ hδsmall
  obtain ⟨q, hq, hfamily⟩ := hmain P a s G
  exact ⟨C2, q, hC2, hq, hfamily L⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
