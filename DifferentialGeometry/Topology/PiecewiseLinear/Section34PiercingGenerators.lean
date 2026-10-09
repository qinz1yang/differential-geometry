import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingNonempty

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_homeomorph_image_of_compact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {T : Set X} {f : X → Y}
    (hT : IsCompact T) (hf : ContinuousOn f T) (hinj : InjOn f T) :
    ∃ φ : T ≃ₜ f '' T, ∀ x : T, (φ x : Y) = f x := by
  let _ : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let e := Equiv.Set.imageOfInjOn f T hinj
  have he : Continuous e := hf.domRestrict.subtype_mk _
  exact ⟨he.homeoOfEquivCompactToT2, fun _ => rfl⟩

theorem CarriesFundamentalGroupOnto.image_of_compact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {J T : Set X} {f : X → Y}
    (hcarry : CarriesFundamentalGroupOnto J T) (hT : IsCompact T)
    (hf : ContinuousOn f T) (hinj : InjOn f T) :
    CarriesFundamentalGroupOnto (f '' J) (f '' T) := by
  obtain ⟨φ, hφ⟩ := exists_homeomorph_image_of_compact hT hf hinj
  refine carriesFundamentalGroupOnto_of_homeomorph (image_mono hcarry.1) hcarry.1
    φ.symm ?_ hcarry
  intro y
  have hy : f (φ.symm y) = y := (hφ _).symm.trans
    (congrArg Subtype.val (φ.apply_symm_apply y))
  constructor
  · rintro ⟨x, hx, hxy⟩
    have heq := hinj (hcarry.1 hx) (φ.symm y).2 (hxy.trans hy.symm)
    exact heq ▸ hx
  · exact fun hx => ⟨φ.symm y, hx, hy⟩

theorem IsTopologicalSolidTorus.image_of_continuousOn_injOn {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {S : Set X} {f : X → Y}
    (hS : IsTopologicalSolidTorus S) (hf : ContinuousOn f S) (hinj : InjOn f S) :
    IsTopologicalSolidTorus (f '' S) := by
  obtain ⟨ψ⟩ := hS
  have hScompact : IsCompact S := isCompact_iff_compactSpace.mpr ψ.symm.compactSpace
  obtain ⟨φ, -⟩ := exists_homeomorph_image_of_compact hScompact hf hinj
  exact ⟨φ.symm.trans ψ⟩

theorem IsPLCellOn.simplyConnectedSpace {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {D B : Set M}
    (hD : IsPLCellOn d D B) : SimplyConnectedSpace D := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hD
  have hP : IsPLBall d P := ⟨r, hr⟩
  let _ := hP.simplyConnectedSpace
  obtain ⟨φ, -⟩ := exists_homeomorph_image_of_compact hP.isPolyhedron.isCompact
    hu.continuousOn hu.injOn
  exact φ.symm.toHomotopyEquiv.simplyConnectedSpace

theorem IsTopologicalSolidTorus.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S D B K : Set M}
    (hS : IsTopologicalSolidTorus S) (hD : IsPLCellOn d D B)
    (hDS : D ⊆ S) (hK : K.Nonempty) (hKD : K ⊆ D) :
    ¬ CarriesFundamentalGroupOnto K S := by
  rintro ⟨hKS, hcarry⟩
  obtain ⟨b, hb⟩ := hK
  have hsurj := hcarry hKS ⟨b, hb⟩
  let _ := hD.simplyConnectedSpace
  let _ : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp hS.isPathConnected
  apply hS.not_simplyConnectedSpace
  refine (simplyConnectedSpace_iff_fundamentalGroup_eq_one (⟨b, hKS hb⟩ : S)).mpr fun g => ?_
  obtain ⟨a, rfl⟩ := hsurj g
  let iKD : C(K, D) := ⟨inclusion hKD, continuous_inclusion hKD⟩
  let iDS : C(D, S) := ⟨inclusion hDS, continuous_inclusion hDS⟩
  have hcomp := DFunLike.congr_fun (fundamentalGroup_map_continuousMap_comp iKD iDS ⟨b, hb⟩) a
  rw [MonoidHom.comp_apply, Subsingleton.elim (FundamentalGroup.map iKD _ a) 1, map_one] at hcomp
  exact hcomp

theorem IsAnnulusOn.ends_nonempty {M : Type*} [TopologicalSpace M] {A A₀ A₁ : Set M}
    (hA : IsAnnulusOn A A₀ A₁) : A₀.Nonempty ∧ A₁.Nonempty := by
  obtain ⟨φ, rfl, rfl⟩ := hA
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  constructor
  · exact ⟨φ (⟨x, hx⟩, ⟨0, by norm_num⟩), ⟨_, ⟨_, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨φ (⟨x, hx⟩, ⟨1, by norm_num⟩), ⟨_, ⟨_, rfl, rfl⟩, rfl⟩⟩

theorem IsAnnulusOn.image_of_continuousOn_injOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {A A₀ A₁ : Set X} {f : X → Y}
    (hA : IsAnnulusOn A A₀ A₁) (hf : ContinuousOn f A) (hinj : InjOn f A) :
    IsAnnulusOn (f '' A) (f '' A₀) (f '' A₁) := by
  obtain ⟨ψ, hψ⟩ := exists_homeomorph_image_of_compact hA.isCompact hf hinj
  obtain ⟨φ, h₀, h₁⟩ := hA
  have himage (S : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1)) :
      f '' (Subtype.val '' (φ '' S)) = Subtype.val '' ((φ.trans ψ) '' S) := by
    simp only [image_image]
    exact image_congr fun x _ => (hψ (φ x)).symm
  exact ⟨φ.trans ψ, h₀ ▸ himage _, h₁ ▸ himage _⟩

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

theorem section34_piercing_annuli
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    IsAnnulusOn (G (ends e).1 '' Aa e) (G (ends e).1 '' Ab₀ e) (G (ends e).1 '' Ab₁ e) ∧
      IsAnnulusOn (G (ends e).2 '' Bb e) (G (ends e).2 '' Bb₀ e) (G (ends e).2 '' Bb₁ e) := by
  obtain ⟨-, -, hsub, -, hCp, -, -, -, -, -, -, htor, hSnCc, -, hAa, hBb, -⟩ := hprep
  obtain ⟨hG, -⟩ := hpack
  have hACc : Aa e ⊆ Cc (ends e).1 := by
    rw [(hAa e).1]
    exact inter_subset_right.trans (((htor e).1.trans interior_subset).trans
      (hSnCc e (ends e).1 (Or.inl rfl)))
  have hBCc := ((hBb e).1.trans (hCp _).boundary_subset).trans (hsub _).2.1
  exact ⟨(hAa e).2.image_of_continuousOn_injOn
      ((hG _).continuousOn.mono hACc) ((hG _).injOn.mono hACc),
    (hBb e).2.image_of_continuousOn_injOn
      ((hG _).continuousOn.mono hBCc) ((hG _).injOn.mono hBCc)⟩

theorem section34_tubes_are_topological_solid_tori
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    IsTopologicalSolidTorus (Sp e) ∧ IsTopologicalSolidTorus (Tp e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  obtain ⟨hG, -, -, htube, -⟩ := hpack
  have hS := hSnCc e (ends e).1 (Or.inl rfl)
  have hT := ((htor e).1.trans interior_subset).trans hS
  rw [(htube e).1, (htube e).2]
  exact ⟨(htor e).2.1.image_of_continuousOn_injOn
    ((hG _).continuousOn.mono hS) ((hG _).injOn.mono hS),
    (htor e).2.2.1.image_of_continuousOn_injOn
      ((hG _).continuousOn.mono hT) ((hG _).injOn.mono hT)⟩

theorem section34_inner_tube_subset_interior_outer
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    Tp e ⊆ interior (Sp e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  obtain ⟨hG, -, -, htube, -⟩ := hpack
  have hsub := interior_subset.trans (hSnCc e (ends e).1 (Or.inl rfl))
  have hopen : IsOpen (G (ends e).1 '' interior (Sn e)) :=
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) isOpen_interior
      ((hG _).continuousOn.mono hsub) ((hG _).injOn.mono hsub)
  rw [(htube e).1, (htube e).2]
  exact (image_mono (htor e).1).trans
    (interior_maximal (image_mono interior_subset) hopen)

theorem section34_piercing_generators
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    CarriesFundamentalGroupOnto (G (ends e).1 '' Ab₀ e) (Tp e) ∧
      CarriesFundamentalGroupOnto (G (ends e).1 '' Ab₁ e) (Tp e) ∧
      CarriesFundamentalGroupOnto (G (ends e).1 '' Ab₀ e) (Sp e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -, -, -, -, -, -, -, -, -, hgen, -⟩ :=
    hprep
  obtain ⟨hG, -, -, htube, -⟩ := hpack
  have hcpt {T : Set M₁} (hT : IsTopologicalSolidTorus T) : IsCompact T := by
    obtain ⟨φ⟩ := hT
    exact isCompact_iff_compactSpace.mpr φ.symm.compactSpace
  have hS := hSnCc e (ends e).1 (Or.inl rfl)
  have hT := ((htor e).1.trans interior_subset).trans hS
  rw [(htube e).1, (htube e).2]
  exact ⟨(hgen e).1.image_of_compact (hcpt (htor e).2.2.1)
      ((hG _).continuousOn.mono hT) ((hG _).injOn.mono hT),
    (hgen e).2.1.image_of_compact (hcpt (htor e).2.2.1)
      ((hG _).continuousOn.mono hT) ((hG _).injOn.mono hT),
    (hgen e).2.2.image_of_compact (hcpt (htor e).2.1)
      ((hG _).continuousOn.mono hS) ((hG _).injOn.mono hS)⟩

theorem section34_piercing_ends_not_in_inner_cell
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {d : ℕ} {D B : Set M₂} (hD : IsPLCellOn d D B) (hDT : D ⊆ Tp e) :
    ¬ G (ends e).1 '' Ab₀ e ⊆ D ∧ ¬ G (ends e).1 '' Ab₁ e ⊆ D := by
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).2
  have hgen := section34_piercing_generators hprep hpack e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨h₀, h₁⟩ := (hAa e).2.ends_nonempty
  exact ⟨fun hsub => htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD hDT
      (h₀.image _) hsub hgen.1,
    fun hsub => htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD hDT
      (h₁.image _) hsub hgen.2.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
