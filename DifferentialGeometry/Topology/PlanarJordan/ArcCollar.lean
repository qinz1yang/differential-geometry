import DifferentialGeometry.External.Schoenflies.PolyArcRealize

open Set Topology

namespace Schoenflies

theorem exists_hasArcCollars_of_polygonal_subarc
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {a b : ℝ} (ha : a ∈ unitInterval) (hb : b ∈ unitInterval) (hab : a < b)
    (hpoly : IsPolygonal (f '' Icc a b)) {U : Set Plane} (hU : IsOpen U)
    (hsub : f '' Ioo a b ⊆ U) :
    ∃ V : Set Plane, IsOpen V ∧ V ⊆ U ∧ f '' Ioo a b ⊆ V ∧
      V ∩ f '' unitInterval = f '' Ioo a b ∧ HasArcCollars V (f '' unitInterval) := by
  let Z := f '' Icc 0 a ∪ f '' Icc b 1
  have hZ : IsClosed Z :=
    ((isCompact_Icc.image_of_continuousOn (hf.mono (Icc_subset_Icc_right ha.2))).union
      (isCompact_Icc.image_of_continuousOn (hf.mono (Icc_subset_Icc_left hb.1)))).isClosed
  let V := U \ Z
  have hV : IsOpen V := hU.sdiff hZ
  have hIV : f '' Ioo a b ⊆ V := by
    rintro x ⟨t, ht, rfl⟩
    have htI : t ∈ unitInterval := ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩
    refine ⟨hsub (mem_image_of_mem f ht), ?_⟩
    rintro (⟨s, hs, heq⟩ | ⟨s, hs, heq⟩)
    · have hst := hi ⟨hs.1, hs.2.trans ha.2⟩ htI heq
      exact ht.1.not_ge (hst ▸ hs.2)
    · have hst := hi ⟨hb.1.trans hs.1, hs.2⟩ htI heq
      exact ht.2.not_ge (hst ▸ hs.1)
  have hVA : V ∩ f '' unitInterval = f '' Ioo a b := by
    apply Subset.antisymm
    · rintro x ⟨hx, t, ht, rfl⟩
      refine mem_image_of_mem f ⟨?_, ?_⟩
      · by_contra h
        exact hx.2 (Or.inl (mem_image_of_mem f ⟨ht.1, not_lt.mp h⟩))
      · by_contra h
        exact hx.2 (Or.inr (mem_image_of_mem f ⟨not_lt.mp h, ht.2⟩))
    · intro x hx
      exact ⟨hIV hx, (image_mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha.1 hb.2))) hx⟩
  have hfa : f a ∉ V := fun hx => hx.2 (Or.inl (mem_image_of_mem f ⟨ha.1, le_rfl⟩))
  have hfb : f b ∉ V := fun hx => hx.2 (Or.inr (mem_image_of_mem f ⟨le_rfl, hb.2⟩))
  have hP : IsArcBetween (f '' Icc a b) (f a) (f b) := by
    simpa only [uIcc_of_le hab.le] using isArcBetween_subarc_of_injOn_I hf hi ha hb hab.ne
  have hPD : (f '' Icc a b) \ {f a, f b} ⊆ V := by
    rintro x ⟨⟨t, ht, rfl⟩, hends⟩
    apply hIV
    refine mem_image_of_mem f ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
    · intro hat
      exact hends (Or.inl (congrArg f hat.symm))
    · intro htb
      exact hends (Or.inr (congrArg f htb))
  have hlocal := hasArcCollars_of_isPolygonal hV hfa hfb hPD hP hpoly
  refine ⟨V, hV, sdiff_subset, hIV, hVA, ?_⟩
  intro K hK hKcompact hKconn hKnt
  have hKP : K ⊆ V ∩ f '' Icc a b := fun x hx =>
    ⟨(hK hx).1, image_mono Ioo_subset_Icc_self (hVA.subset (hK hx))⟩
  obtain ⟨C⟩ := hlocal K hKP hKcompact hKconn hKnt
  have hdiff : C.nbhd \ f '' unitInterval = C.nbhd \ f '' Icc a b := by
    apply Subset.antisymm
    · exact sdiff_subset_sdiff Subset.rfl (image_mono (Icc_subset_Icc ha.1 hb.2))
    · rintro x ⟨hx, hnot⟩
      refine ⟨hx, fun hA => hnot ?_⟩
      exact image_mono Ioo_subset_Icc_self (hVA.subset ⟨C.nbhd_subset hx, hA⟩)
  exact ⟨{
    nbhd := C.nbhd
    left := C.left
    right := C.right
    isOpen_nbhd := C.isOpen_nbhd
    subset_nbhd := C.subset_nbhd
    nbhd_subset := C.nbhd_subset
    nbhd_diff := hdiff.trans C.nbhd_diff
    isConnected_left := C.isConnected_left
    isConnected_right := C.isConnected_right
    subset_closure_left := C.subset_closure_left
    subset_closure_right := C.subset_closure_right }⟩

open Classical in
theorem ArcCollar.exists_isOpen_connected_chain
    {P : Set Plane} (hP : IsClosed P) {D K : ℕ → Set Plane}
    (hD : ∀ n, IsOpen (D n)) (C : ∀ n, ArcCollar (D n) P (K n))
    (hK : ∀ n, (K n ∩ K (n + 1)).Nonempty) :
    ∃ O : ℕ → Set Plane,
      (∀ n, IsOpen (O n) ∧ IsConnected (O n) ∧ O n ⊆ D n \ P ∧ K n ⊆ closure (O n)) ∧
      ∀ n, (O n ∩ O (n + 1)).Nonempty := by
  let T (n : ℕ) (b : Bool) : Set Plane := Bool.rec (C n).left (C n).right b
  have hT (n : ℕ) (b : Bool) :
      IsConnected (T n b) ∧ T n b ⊆ D n \ P ∧ K n ⊆ closure (T n b) := by
    cases b with
    | false => exact ⟨(C n).isConnected_left, (C n).left_subset_diff, (C n).subset_closure_left⟩
    | true => exact ⟨(C n).isConnected_right, (C n).right_subset_diff, (C n).subset_closure_right⟩
  have hstep (n : ℕ) (b : Bool) : ∃ c : Bool, (T n b ∩ T (n + 1) c).Nonempty := by
    obtain ⟨x, hx, hx'⟩ := hK n
    obtain ⟨y, hyN, hyT⟩ := mem_closure_iff.mp ((hT n b).2.2 hx)
      (C (n + 1)).nbhd (C (n + 1)).isOpen_nbhd ((C (n + 1)).subset_nbhd hx')
    have hy := (C (n + 1)).nbhd_diff.subset ⟨hyN, ((hT n b).2.1 hyT).2⟩
    rcases hy with hy | hy
    · exact ⟨false, y, hyT, hy⟩
    · exact ⟨true, y, hyT, hy⟩
  choose next hnext using hstep
  let b : ℕ → Bool := Nat.rec false (fun n c => next n c)
  choose z hz using fun n => (hT n (b n)).1.nonempty
  let O (n : ℕ) := connectedComponentIn (D n \ P) (z n)
  have hTO (n : ℕ) : T n (b n) ⊆ O n :=
    (hT n (b n)).1.isPreconnected.subset_connectedComponentIn (hz n) (hT n (b n)).2.1
  refine ⟨O, ?_, ?_⟩
  · intro n
    exact ⟨Plane.isOpen_connectedComponentIn ((hD n).sdiff hP),
      isConnected_connectedComponentIn_iff.mpr ((hT n (b n)).2.1 (hz n)),
      connectedComponentIn_subset _ _, (hT n (b n)).2.2.trans (closure_mono (hTO n))⟩
  · intro n
    have hmeet : (T n (b n) ∩ T (n + 1) (b (n + 1))).Nonempty := hnext n (b n)
    exact hmeet.mono (inter_subset_inter (hTO n) (hTO (n + 1)))
end Schoenflies
