import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentBandMatching
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentOrientedBands
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterMatchedAnnularRegion
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPrism

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem lateral_image_homeomorphInto {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P)
    {f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)))
    (hfP : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P) :
    IsPLHomeomorphInto 3 u (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) := by
  have hp := hf.isPiecewiseAffineOn.isPolyhedron_image
    (isPolyhedron_stdSimplexBoundary_two.prod isHPolytope_Icc.isPolyhedron)
  exact (hu.isPLOn.mono_of_isPolyhedron hp hfP).isPLHomeomorphInto_model
    hp.isCompact (hu.injOn.mono hfP)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_current_simultaneous_empty_bands
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {X As Y Bs A A₀ A₁ B B₀ B₁ : Set M₂}
    (hX : IsPLCellOn 3 X As) (hY : IsPLCellOn 3 Y Bs)
    (hA : IsAnnulusOn A A₀ A₁) (hB : IsAnnulusOn B B₀ B₁)
    (hAAs : A ⊆ As) (hBBs : B ⊆ Bs)
    (hAS : A ⊆ interior (Sp e)) (hBS : B ⊆ interior (Sp e))
    {n : ℕ} (hn : 1 < n) (Γ : Fin n → Set M₂)
    (hΓ : ∀ i, IsPolyhedralSphere (n := 3) 1 (Γ i))
    (hΓA : ∀ i, Γ i ⊆ A) (hΓB : ∀ i, Γ i ⊆ B)
    (hΓAend : ∀ i, Disjoint (Γ i) (A₀ ∪ A₁))
    (hΓBend : ∀ i, Disjoint (Γ i) (B₀ ∪ B₁))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j))
    (hcarry : ∀ i, CarriesFundamentalGroupOnto (Γ i) (Sp e))
    (htrace : As ∩ Bs = ⋃ i, Γ i)
    (hcross : ∀ x ∈ As ∩ Bs,
      ∃ c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)), x ∈ c.source ∧
        HasPLCrossingAt (c '' (Bs ∩ c.source)) (c '' (As ∩ c.source)) (c x)) :
    ∃ i j : Fin n, i ≠ j ∧
      ∃ (P Q' : Set (EuclideanSpace ℝ (Fin 3)))
        (u v : EuclideanSpace ℝ (Fin 3) → M₂)
        (f g : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = X ∧
      IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = Γ i ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = Γ j ∧
      Disjoint ((u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) Bs ∧
      IsPLBall 3 Q' ∧ IsPLHomeomorphInto 3 v Q' ∧ v '' Q' = Y ∧
      IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ Q' ∧
      (v ∘ g) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B ∧
      (v ∘ g) '' (stdSimplexBoundary 2 ×ˢ {0}) = Γ i ∧
      (v ∘ g) '' (stdSimplexBoundary 2 ×ˢ {1}) = Γ j ∧
      Disjoint ((v ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) As := by
  classical
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).1
  have hess (Z : Set M₂) (hZS : Z ⊆ Sp e) (i : Fin n) :
      ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Γ i) ∧ D ⊆ Z := by
    rintro ⟨D, hD, hDZ⟩
    obtain ⟨p, hp⟩ := hΓ i
    have hne : (Γ i).Nonempty := p.piece.bijOn.image_eq ▸ hp.nonempty.image p.piece.map
    exact htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD
      (hDZ.trans hZS) hne hD.boundary_subset (hcarry i)
  obtain ⟨σA, E₀, E₁, hcapA, -, -, hdisA, hleftA, hrightA⟩ :=
    hX.exists_ordered_disk_caps_of_essential_sequence hA hAAs Γ hΓ hΓA hΓAend hΓdis
      (hess A (hAS.trans interior_subset))
  obtain ⟨σB, D₀, D₁, hcapB, hmonoB, hantiB, hdisB, hleftB, hrightB⟩ :=
    hY.exists_ordered_disk_caps_of_essential_sequence hB hBBs Γ hΓ hΓB hΓBend hΓdis
      (hess B (hBS.trans interior_subset))
  have htraceA : A ∩ Bs ⊆ ⋃ i, Γ (σA i) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (htrace.subset ⟨hAAs hx.1, hx.2⟩)
    exact mem_iUnion.mpr ⟨σA.symm i, by simpa only [σA.apply_symm_apply] using hi⟩
  have htraceB : B ∩ As ⊆ ⋃ i, Γ (σB i) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (htrace.subset ⟨hx.2, hBBs hx.1⟩)
    exact mem_iUnion.mpr ⟨σB.symm i, by simpa only [σB.apply_symm_apply] using hi⟩
  have hbandsB := hY.exists_lateral_bands_of_ordered_caps hB hBBs hcapB hdisB hleftB
    hrightB (fun i => hΓB (σB i)) (fun i => hΓBend (σB i)) htraceB
  have hex (r : Fin (n - 1)) := hbandsB ⟨r.val, by omega⟩ ⟨r.val + 1, by omega⟩
    (by exact_mod_cast Nat.lt_succ_self r.val)
  choose P u g hcert using hex
  let q (r : ℕ) : Fin (n - 1) :=
    if hr : r < n - 1 then ⟨r, hr⟩ else ⟨0, by omega⟩
  have hq (r : ℕ) (hr : r + 1 < n) : (q r).val = r := by
    simp only [q, dite_eq_left (show r < n - 1 by omega)]
  let p := σB.trans σA.symm
  have hp (i : Fin n) : σA (p i) = σB i := σA.apply_symm_apply _
  let fB := fun r => u (q r) ∘ g (q r)
  have hchosen (r : ℕ) (hr : r + 1 < n) :
      ContinuousOn (fB r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      InjOn (fB r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      fB r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        D₁ ⟨r, by omega⟩ ∩ D₀ ⟨r + 1, hr⟩ ∧
      fB r '' (stdSimplexBoundary 2 ×ˢ {0}) = Γ (σA (p ⟨r, by omega⟩)) ∧
      fB r '' (stdSimplexBoundary 2 ×ˢ {1}) = Γ (σA (p ⟨r + 1, hr⟩)) ∧
      Disjoint (fB r '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) As := by
    obtain ⟨-, hu, -, hg, hgP, himage, -, hzero, hone, -, hempty⟩ := hcert (q r)
    have hmap : MapsTo (g (q r)) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (P (q r)) :=
      fun x hx => hgP ⟨x, hx, rfl⟩
    refine ⟨hu.continuousOn.comp hg.isPiecewiseAffineOn.continuousOn hmap,
      hu.injOn.comp hg.bijOn.injOn hmap, ?_, ?_, ?_, hempty rfl⟩
    · simpa only [hq r hr] using himage
    · simpa only [hp, hq r hr] using hzero
    · simpa only [hp, hq r hr] using hone
  have hbandsA := hX.exists_oriented_lateral_band_of_ordered_caps hA hAAs hcapA hdisA
    hleftA hrightA (fun i => hΓA (σA i)) (fun i => hΓAend (σA i)) htraceA
  have hregions (r : ℕ) (hr : r + 1 < n) : ∃ C F : Set M₂,
      closure (interior C) = C ∧
      frontier C = fB r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪ F ∧
      As ∩ C = F ∧ (C ⊆ X ∨ C ∩ X ⊆ As) ∧
      ∀ t, Γ (σA t) ⊆ F ↔ min (p ⟨r, by omega⟩) (p ⟨r + 1, hr⟩) ≤ t ∧
        t ≤ max (p ⟨r, by omega⟩) (p ⟨r + 1, hr⟩) := by
    let i : Fin n := ⟨r, by omega⟩
    let j : Fin n := ⟨r + 1, hr⟩
    have hij : i ≠ j := by intro hh; have := congrArg Fin.val hh; dsimp [i, j] at this; omega
    obtain ⟨Q', w, f, -, hw, -, hf, hfQ, -, hfA, hfzero, hfone, hint, -⟩ :=
      hbandsA (p i) (p j) (p.injective.ne hij)
    obtain ⟨-, hu, -, hg, hgP, -, hgB, hgzero, hgone, -, hempty⟩ := hcert (q r)
    have hz : (u (q r) ∘ g (q r)) '' (stdSimplexBoundary 2 ×ˢ {0}) = Γ (σB i) := by
      simpa only [hq r hr, i] using hgzero
    have ho : (u (q r) ∘ g (q r)) '' (stdSimplexBoundary 2 ×ˢ {1}) = Γ (σB j) := by
      simpa only [hq r hr, j] using hgone
    have hfz : (w ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = Γ (σB i) := by
      simpa only [hp] using hfzero
    have hfo : (w ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = Γ (σB j) := by
      simpa only [hp] using hfone
    have hDfull : u (q r) '' (g (q r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) =
        fB r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := (image_comp _ _ _).symm
    have hFfull : w '' (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) =
        (w ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := (image_comp _ _ _).symm
    obtain ⟨P', v, R, -, -, -, -, -, -, -, -, -, -, -, -, hreg, -, hfront, hfirst, hside⟩ :=
      exists_section34_outer_region_of_empty_second_band hprep hpack e hX hA hAAs hAS
        (hΓ (σB i)) (hΓ (σB j)) (hΓdis (σB.injective.ne hij))
        (hΓAend (σB i)) (hΓAend (σB j)) (hcarry (σB i)) (hcarry (σB j))
        (lateral_image_homeomorphInto hu hg hgP) (lateral_image_homeomorphInto hw hf hfQ)
        hg hf (by rw [hDfull]; exact hgB.trans hBS) (by rw [hFfull]; exact hfA)
        hz ho hfz hfo (hempty rfl)
    rw [hDfull, hFfull] at hfront
    rw [hFfull] at hfirst hside
    refine ⟨v '' R.space, (w ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1),
      hreg, hfront, hfirst, ?_, hint⟩
    exact hside.imp id fun hs => hs.subset.trans (hfA.trans hAAs)
  obtain ⟨i, j, hij, hadj⟩ := hX.exists_common_adjacent_pair_of_current_bands hn hY hcross p
    (fun r => (hΓA (σA r)).trans hAAs)
    (fun r s hrs => hΓdis (σA.injective.ne hrs))
    (fun r => by
      simpa only [hp] using
        And.intro (hcapB r).1 ⟨(hcapB r).2.1, (hcapB r).2.2.1, (hcapB r).2.2.2.1⟩)
    hmonoB.monotone hantiB.antitone hdisB hchosen hregions
  have hi : i.val + 1 < n := hij ▸ j.isLt
  have hneq : i ≠ j := by intro hh; have := congrArg Fin.val hh; omega
  obtain ⟨Q', v, f, hQ, hv, hvQ, hf, hfQ, -, hfA, hfzero, hfone, -, hfempty⟩ :=
    hbandsA (p i) (p j) (p.injective.ne hneq)
  obtain ⟨hP, hu, huP, hg, hgP, -, hgB, hgzero, hgone, -, hgempty⟩ := hcert (q i.val)
  refine ⟨σB i, σB j, σB.injective.ne hneq, Q', P (q i.val), v, u (q i.val),
    f, g (q i.val), hQ, hv, hvQ, hf, hfQ, hfA, ?_, ?_, hfempty hadj,
    hP, hu, huP, hg, hgP, hgB, ?_, ?_, hgempty rfl⟩
  · simpa only [hp] using hfzero
  · simpa only [hp] using hfone
  · simpa only [hq i.val hi, Fin.eta] using hgzero
  · simpa only [hq i.val hi, hij] using hgone

end DifferentialGeometry.Topology.PiecewiseLinear
