import Mathlib
import PEqualNP.Defs

open Finset SimpleGraph

private lemma nat_le_of_int_sub_le {a b k : ℕ} (h : (a : ℤ) - (b : ℤ) ≤ (k : ℤ)) : a ≤ b + k := by
  omega

private lemma nat_sub_add_eq_sub_sub {a b c : ℕ} (hba : b ≤ a) (hcb : c ≤ b) :
    a - b + c = a - (b - c) := by
  omega

theorem PEqualNP.Outside.L_meta_533 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) →
      ∃ (M : Finset (Sym2 (Fin n))) (T : Finset (Fin n)),
        (∀ e ∈ M, e ∈ G.edgeFinset) ∧
        (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : Fin n, v ∈ e → v ∉ f) ∧
        (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        T.card = M.card := by
  classical
  intro n G _ hcol
  obtain ⟨c, hc⟩ := hcol
  let left : Finset (Fin n) := univ.filter fun v => c v = false
  have mem_left : ∀ u, u ∈ left ↔ c u = false := by
    intro u
    simp [left]
  let nbr : Finset (Fin n) → Finset (Fin n) := fun S => S.biUnion fun u => G.neighborFinset u
  have mem_nbr : ∀ (S : Finset (Fin n)) (v : Fin n), v ∈ nbr S ↔ ∃ u ∈ S, G.Adj u v := by
    intro S v
    simp [nbr, mem_biUnion, mem_neighborFinset]
  have hnbr_empty : nbr ∅ = ∅ := by
    simp [nbr]
  obtain ⟨S0, hS0mem, hS0max⟩ :=
    exists_max_image left.powerset (fun S => (S.card : ℤ) - ((nbr S).card : ℤ))
      ⟨∅, empty_mem_powerset _⟩
  have hS0sub : S0 ⊆ left := mem_powerset.mp hS0mem
  have hN0 : (nbr S0).card ≤ S0.card := by
    have h0 := hS0max ∅ (empty_mem_powerset _)
    rw [hnbr_empty] at h0
    simpa using h0
  let d : ℕ := S0.card - (nbr S0).card
  have hd_int : (S0.card : ℤ) - ((nbr S0).card : ℤ) = d := by
    rw [← Nat.cast_sub hN0]
  have hdef_le : ∀ S ⊆ left, S.card ≤ (nbr S).card + d := by
    intro S hS
    apply nat_le_of_int_sub_le
    rw [← hd_int]
    exact hS0max S (mem_powerset.mpr hS)
  let T : Finset (Fin n) := (left \ S0) ∪ nbr S0
  have hTdisj : Disjoint (left \ S0) (nbr S0) := by
    rw [Finset.disjoint_left]
    intro v hvT hvN
    have hvL : v ∈ left := (mem_sdiff.mp hvT).1
    have hvfalse : c v = false := (mem_left v).mp hvL
    obtain ⟨u, hu, huv⟩ := (mem_nbr S0 v).mp hvN
    have hufalse : c u = false := (mem_left u).mp (hS0sub hu)
    exact hc u v huv (hufalse.trans hvfalse.symm)
  have hTcard : T.card = left.card - d := by
    have hinter : S0 ∩ left = S0 := Finset.inter_eq_left.mpr hS0sub
    rw [show T = (left \ S0) ∪ nbr S0 from rfl, card_union_of_disjoint hTdisj, card_sdiff, hinter]
    exact nat_sub_add_eq_sub_sub (card_le_card hS0sub) hN0
  have hcover : ∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    by_cases hu : c u = false
    · by_cases hSu : u ∈ S0
      · exact Or.inr (mem_union_right _ ((mem_nbr S0 v).mpr ⟨u, hSu, huv⟩))
      · exact Or.inl (mem_union_left _ (mem_sdiff.mpr ⟨(mem_left u).mpr hu, hSu⟩))
    · have hv : c v = false := by
        cases hcv : c v
        · rfl
        · cases hcu : c u
          · exact (hu hcu).elim
          · exact (hc u v huv (hcu.trans hcv.symm)).elim
      by_cases hSv : v ∈ S0
      · exact Or.inl (mem_union_right _ ((mem_nbr S0 u).mpr ⟨v, hSv, huv.symm⟩))
      · exact Or.inr (mem_union_left _ (mem_sdiff.mpr ⟨(mem_left v).mpr hv, hSv⟩))
  let adj2 : (Fin n ⊕ Fin d) → (Fin n ⊕ Fin d) → Prop := fun a b =>
    match a, b with
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr _ => c u = false
    | .inr _, .inl u => c u = false
    | .inr _, .inr _ => False
  let G2 : SimpleGraph (Fin n ⊕ Fin d) := {
    Adj := adj2
    symm := by
      refine ⟨?_⟩
      intro a b h
      match a, b with
      | .inl u, .inl v =>
          simpa [adj2, adj_comm] using h
      | .inl u, .inr i =>
          simpa [adj2] using h
      | .inr i, .inl u =>
          simpa [adj2] using h
      | .inr i, .inr j =>
          simp [adj2] at h
    loopless := by
      refine ⟨?_⟩
      intro a h
      match a with
      | .inl u =>
          exact G.loopless.irrefl u h
      | .inr i =>
          simp [adj2] at h
  }
  have adj_iff : ∀ a b, G2.Adj a b ↔ adj2 a b := by
    intro a b
    rfl
  have : DecidableRel G2.Adj := fun _ _ => Classical.propDecidable _
  have : LocallyFinite G2 := fun _ => Fintype.ofFinite _
  let p1 : Set (Fin n ⊕ Fin d) := {x | ∃ u, x = Sum.inl u ∧ c u = false}
  let p2 : Set (Fin n ⊕ Fin d) :=
    {x | (∃ u, x = Sum.inl u ∧ c u = true) ∨ (∃ i, x = Sum.inr i)}
  have hbip : G2.IsBipartiteWith p1 p2 := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hx1 hx2
      simp only [p1, p2, Set.mem_ofPred_eq] at hx1 hx2
      obtain ⟨u, rfl, hu⟩ := hx1
      rcases hx2 with ⟨v, hxv, hv⟩ | ⟨i, hi⟩
      · cases hxv
        exact Bool.false_ne_true (hu.symm.trans hv)
      · cases hi
    · intro a b hab
      rw [adj_iff] at hab
      match a, b with
      | .inl u, .inl v =>
          have hne := hc u v hab
          cases hcu : c u <;> cases hcv : c v
          · exact (hne (hcu.trans hcv.symm)).elim
          · exact Or.inl (And.intro ⟨u, rfl, hcu⟩ (Or.inl ⟨v, rfl, hcv⟩))
          · exact Or.inr (And.intro (Or.inl ⟨u, rfl, hcu⟩) ⟨v, rfl, hcv⟩)
          · exact (hne (hcu.trans hcv.symm)).elim
      | .inl u, .inr i =>
          exact Or.inl (And.intro ⟨u, rfl, hab⟩ (Or.inr ⟨i, rfl⟩))
      | .inr i, .inl u =>
          exact Or.inr (And.intro (Or.inr ⟨i, rfl⟩) ⟨u, rfl, hab⟩)
      | .inr _, .inr _ =>
          simp [adj2] at hab
  have hhall : ∀ s ⊆ p1, s.ncard ≤ (⋃ x ∈ s, G2.neighborSet x).ncard := by
    intro s hs
    let S : Finset (Fin n) := left.filter fun u => Sum.inl u ∈ s
    have hSsub : S ⊆ left := filter_subset _ _
    have hcard_s : s.ncard = S.card := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_congr (fun x hx => Classical.choose (hs hx)) ?_ ?_ ?_
      · intro x hx
        have spec := Classical.choose_spec (hs hx)
        rw [Finset.mem_coe]
        refine mem_filter.mpr ⟨(mem_left _).mpr spec.2, ?_⟩
        have hx' : x ∈ s := hx
        rwa [spec.1] at hx'
      · intro a b ha hb h
        have sa := (Classical.choose_spec (hs ha)).1
        have sb := (Classical.choose_spec (hs hb)).1
        rw [sa, sb, h]
      · intro u hu
        have huS := Finset.mem_coe.mp hu
        refine ⟨Sum.inl u, (mem_filter.mp huS).2, ?_⟩
        exact (Sum.inl_injective (Classical.choose_spec (hs (mem_filter.mp huS).2)).1).symm
    by_cases hSe : S = ∅
    · have hsempty : s = ∅ := by
        ext x
        constructor
        · intro hx
          obtain ⟨u, rfl, hu⟩ := hs hx
          have huS : u ∈ S := mem_filter.mpr ⟨(mem_left u).mpr hu, hx⟩
          exact (Finset.notMem_empty u) (by rwa [← hSe])
        · simp
      rw [hsempty, Set.ncard_empty]
      exact Nat.zero_le _
    · have hSne : S.Nonempty := nonempty_of_ne_empty hSe
      obtain ⟨u0, hu0⟩ := hSne
      let Nreal : Finset (Fin n ⊕ Fin d) := (nbr S).image Sum.inl
      let Ndum : Finset (Fin n ⊕ Fin d) := (univ : Finset (Fin d)).image Sum.inr
      let Nfin : Finset (Fin n ⊕ Fin d) := Nreal ∪ Ndum
      have hNdisj : Disjoint Nreal Ndum := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Nreal, Ndum, mem_image] at hx1 hx2
        rcases hx1 with ⟨_, _, rfl⟩
        rcases hx2 with ⟨_, _, h⟩
        cases h
      have hNcard : Nfin.card = (nbr S).card + d := by
        rw [show Nfin = Nreal ∪ Ndum from rfl, card_union_of_disjoint hNdisj]
        have hreal : Nreal.card = (nbr S).card := card_image_of_injective _ Sum.inl_injective
        have hdumc : Ndum.card = d := by
          rw [show Ndum = (univ : Finset (Fin d)).image Sum.inr from rfl,
            card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]
        simp [hreal, hdumc]
      have hset : (⋃ x ∈ s, G2.neighborSet x) = (Nfin : Set _) := by
        ext w
        constructor
        · intro hw
          obtain ⟨x, hx, hadj⟩ := Set.mem_iUnion₂.mp hw
          obtain ⟨u, rfl, hu⟩ := hs hx
          rw [mem_neighborSet, adj_iff] at hadj
          cases w with
          | inl v =>
              rw [Finset.mem_coe]
              refine mem_union_left _ ?_
              simp only [Nreal, mem_image]
              refine ⟨v, ?_, rfl⟩
              exact (mem_nbr S v).mpr ⟨u, mem_filter.mpr ⟨(mem_left u).mpr hu, hx⟩, hadj⟩
          | inr i =>
              rw [Finset.mem_coe]
              refine mem_union_right _ ?_
              simp only [Ndum, mem_image]
              exact ⟨i, mem_univ _, rfl⟩
        · intro hw
          rw [Finset.mem_coe, show Nfin = Nreal ∪ Ndum from rfl, mem_union] at hw
          rcases hw with hw | hw
          · simp only [Nreal, mem_image] at hw
            obtain ⟨v, hv, rfl⟩ := hw
            obtain ⟨u, hu, huv⟩ := (mem_nbr S v).mp hv
            have huS := mem_filter.mp hu
            refine Set.mem_iUnion₂.mpr ⟨Sum.inl u, huS.2, ?_⟩
            rw [mem_neighborSet, adj_iff]
            exact huv
          · simp only [Ndum, mem_image] at hw
            obtain ⟨i, _, rfl⟩ := hw
            have hu0s : Sum.inl u0 ∈ s := (mem_filter.mp hu0).2
            refine Set.mem_iUnion₂.mpr ⟨Sum.inl u0, hu0s, ?_⟩
            rw [mem_neighborSet, adj_iff]
            exact (mem_left u0).mp (mem_filter.mp hu0).1
      rw [hcard_s, hset, Set.ncard_coe_finset, hNcard]
      exact hdef_le S hSsub
  obtain ⟨M, hMverts, hMatch⟩ := exists_isMatching_of_forall_ncard_le hbip hhall
  let realLeft : Finset (Fin n) :=
    left.filter fun u => ∃ v, M.Adj (Sum.inl u) (Sum.inl v)
  let dum : Finset (Fin n) :=
    left.filter fun u => ∃ i, M.Adj (Sum.inl u) (Sum.inr i)
  have hpartner : ∀ u ∈ left, ∃ w, M.Adj (Sum.inl u) w := by
    intro u hu
    have hp : Sum.inl u ∈ p1 := ⟨u, rfl, (mem_left u).mp hu⟩
    exact (hMatch (hMverts hp)).exists
  have hsplit_or : realLeft ∪ dum = left := by
    ext u
    constructor
    · intro hu
      rcases mem_union.mp hu with hu | hu
      · exact (mem_filter.mp hu).1
      · exact (mem_filter.mp hu).1
    · intro hu
      obtain ⟨w, hw⟩ := hpartner u hu
      cases w with
      | inl v =>
          exact mem_union_left _ (mem_filter.mpr ⟨hu, ⟨v, hw⟩⟩)
      | inr i =>
          exact mem_union_right _ (mem_filter.mpr ⟨hu, ⟨i, hw⟩⟩)
  have hsplit_disj : Disjoint realLeft dum := by
    rw [Finset.disjoint_left]
    intro u huR huD
    obtain ⟨v, hv⟩ := (mem_filter.mp huR).2
    obtain ⟨i, hi⟩ := (mem_filter.mp huD).2
    have hp : Sum.inl u ∈ p1 := ⟨u, rfl, (mem_left u).mp (mem_filter.mp huR).1⟩
    exact Sum.inl_ne_inr ((hMatch (hMverts hp)).unique hv hi)
  have hadd : realLeft.card + dum.card = left.card := by
    rw [← card_union_of_disjoint hsplit_disj, hsplit_or]
  have hdum_le : dum.card ≤ d := by
    let f : dum → Fin d := fun u => Classical.choose (mem_filter.mp u.property).2
    have hf : Function.Injective f := by
      intro u u' hff
      have hu := Classical.choose_spec (mem_filter.mp u.property).2
      have hu' := Classical.choose_spec (mem_filter.mp u'.property).2
      have hmem : Sum.inr (f u) ∈ M.verts := (hu.symm).fst_mem
      have hEq := (hMatch hmem).unique hu.symm (by simpa [hff] using hu'.symm)
      exact Subtype.ext (Sum.inl_injective hEq)
    have hcard := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_fin, Fintype.card_coe] using hcard
  have hreal_card : realLeft.card = left.card - dum.card := by
    omega
  have hreal_ge : left.card - d ≤ realLeft.card := by
    rw [hreal_card]
    exact Nat.sub_le_sub_left hdum_le _
  let realMate : Fin n → Fin n := fun u =>
    if h : ∃ v, M.Adj (Sum.inl u) (Sum.inl v) then Classical.choose h else u
  have hmate : ∀ u, u ∈ realLeft → M.Adj (Sum.inl u) (Sum.inl (realMate u)) := by
    intro u hu
    have hex : ∃ v, M.Adj (Sum.inl u) (Sum.inl v) := (mem_filter.mp hu).2
    simpa [realMate, hex] using Classical.choose_spec hex
  have hmate_color : ∀ u, u ∈ realLeft → c (realMate u) = true := by
    intro u hu
    have hcu : c u = false := (mem_left u).mp (mem_filter.mp hu).1
    cases hcm : c (realMate u)
    · exact (hc u (realMate u) (hmate u hu).adj_sub (hcu.trans hcm.symm)).elim
    · rfl
  let Mfin : Finset (Sym2 (Fin n)) := realLeft.image fun u => s(u, realMate u)
  have hMcard : Mfin.card = realLeft.card := by
    refine card_image_of_injOn ?_
    intro u hu u' hu' heq
    have hcu : c u = false := (mem_left u).mp (mem_filter.mp hu).1
    have hcu' : c u' = false := (mem_left u').mp (mem_filter.mp hu').1
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, _⟩ | ⟨h1, _⟩
    · rfl
    · exact (Bool.false_ne_true (hcu.symm.trans (h1 ▸ hmate_color u' hu'))).elim
  have hedge : ∀ e ∈ Mfin, e ∈ G.edgeFinset := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := mem_image.mp he
    rw [mem_edgeFinset, mem_edgeSet]
    exact (hmate u hu).adj_sub
  have hdisjE : ∀ e ∈ Mfin, ∀ f ∈ Mfin, e ≠ f → ∀ v : Fin n, v ∈ e → v ∉ f := by
    intro e he f hf hne v hv hvf
    obtain ⟨u, hu, rfl⟩ := mem_image.mp he
    obtain ⟨u', hu', rfl⟩ := mem_image.mp hf
    have hv1 : v = u ∨ v = realMate u := (Sym2.mem_iff).mp hv
    have hv2 : v = u' ∨ v = realMate u' := (Sym2.mem_iff).mp hvf
    have hcu : c u = false := (mem_left u).mp (mem_filter.mp hu).1
    have hcu' : c u' = false := (mem_left u').mp (mem_filter.mp hu').1
    have hsame : u = u' := by
      rcases hv1 with hvu | hvm <;> rcases hv2 with hvu' | hvm'
      · exact hvu.symm.trans hvu'
      · exact (Bool.false_ne_true
          (hcu.symm.trans (hvu.symm.trans hvm' ▸ hmate_color u' hu'))).elim
      · exact (Bool.false_ne_true
          (hcu'.symm.trans (hvu'.symm.trans hvm ▸ hmate_color u hu))).elim
      · have hmates : realMate u = realMate u' := hvm.symm.trans hvm'
        have ha := (hmate u hu).symm
        have ha' : M.Adj (Sum.inl (realMate u)) (Sum.inl u') := by
          simpa [hmates] using (hmate u' hu').symm
        exact Sum.inl_injective ((hMatch ha.fst_mem).unique ha ha')
    subst hsame
    exact hne rfl
  have hreal_eq : realLeft.card = T.card := by
    apply le_antisymm
    · let emb : Fin n → Fin n := fun u => if u ∈ S0 then realMate u else u
      refine card_le_card_of_injOn emb ?_ ?_
      · intro u hu
        by_cases hSu : u ∈ S0
        · have hemb : emb u = realMate u := by simp [emb, hSu]
          rw [hemb]
          exact mem_union_right _ ((mem_nbr S0 (realMate u)).mpr ⟨u, hSu, (hmate u hu).adj_sub⟩)
        · have hemb : emb u = u := by simp [emb, hSu]
          rw [hemb]
          exact mem_union_left _ (mem_sdiff.mpr ⟨(mem_filter.mp hu).1, hSu⟩)
      · intro u hu u' hu' heq
        by_cases hSu : u ∈ S0 <;> by_cases hSu' : u' ∈ S0
        · have hemu : emb u = realMate u := by simp [emb, hSu]
          have hemu' : emb u' = realMate u' := by simp [emb, hSu']
          rw [hemu, hemu'] at heq
          have ha := (hmate u hu).symm
          have ha' : M.Adj (Sum.inl (realMate u)) (Sum.inl u') := by
            simpa [heq] using (hmate u' hu').symm
          exact Sum.inl_injective ((hMatch ha.fst_mem).unique ha ha')
        · have hemu : emb u = realMate u := by simp [emb, hSu]
          have hemu' : emb u' = u' := by simp [emb, hSu']
          rw [hemu, hemu'] at heq
          exact (Bool.false_ne_true
            (((mem_left u').mp (mem_filter.mp hu').1).symm.trans (heq ▸ hmate_color u hu))).elim
        · have hemu : emb u = u := by simp [emb, hSu]
          have hemu' : emb u' = realMate u' := by simp [emb, hSu']
          rw [hemu, hemu'] at heq
          exact (Bool.false_ne_true
            (((mem_left u).mp (mem_filter.mp hu).1).symm.trans (heq ▸ hmate_color u' hu'))).elim
        · have hemu : emb u = u := by simp [emb, hSu]
          have hemu' : emb u' = u' := by simp [emb, hSu']
          rw [hemu, hemu'] at heq
          exact heq
    · rw [hTcard]
      exact hreal_ge
  refine ⟨Mfin, T, hedge, hdisjE, hcover, ?_⟩
  exact (hMcard.trans hreal_eq).symm
