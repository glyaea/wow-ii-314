import FormalConjectures.Util.ProblemImports

/-! A complete Lean proof of Written on the Wall II, Graph Conjecture 314. -/

open Classical

namespace WrittenOnTheWallII.GraphConjecture314

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def largestInducedPathSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ s : Finset α,
              s.card = n ∧
              (G.induce (s : Set α)).IsTree ∧
              ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 }

private lemma pathGraph_five_isTree : (pathGraph 5).IsTree := by
  letI : DecidableRel (pathGraph 5).Adj := fun u v =>
    decidable_of_iff (u.val + 1 = v.val ∨ v.val + 1 = u.val) pathGraph_adj.symm
  rw [isTree_iff_connected_and_card]
  refine ⟨pathGraph_connected 4, ?_⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card]
  decide

private lemma pathGraph_five_degree_le_two (v : Fin 5) : (pathGraph 5).degree v ≤ 2 := by
  let e : Fin 5 ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  rw [← card_neighborFinset_eq_degree]
  calc
    ((pathGraph 5).neighborFinset v).card =
        (((pathGraph 5).neighborFinset v).map e).card :=
      (Finset.card_map e).symm
    _ ≤ ({v.val - 1, v.val + 1} : Finset ℕ).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      have hadj : (pathGraph 5).Adj v w := by simpa using hw
      rw [pathGraph_adj] at hadj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      change w.val = v.val - 1 ∨ w.val = v.val + 1
      omega
    _ ≤ 2 := Finset.card_le_two

omit [DecidableEq α] in
private lemma degree_eq_of_iso {β : Type*} [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) (v : α) : G.degree v = H.degree (f v) := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  apply Fintype.card_congr
  exact
    { toFun := fun w => ⟨f w.1, f.map_rel_iff.mpr w.2⟩
      invFun := fun w => ⟨f.symm w.1, by simpa using f.symm.map_rel_iff.mpr w.2⟩
      left_inv := fun w => by ext; exact f.symm_apply_apply w.1
      right_inv := fun w => by ext; exact f.apply_symm_apply w.1 }

private lemma five_le_largestInducedPathSize_of_chordlessPath
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {a b c d e : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hae : ¬G.Adj a e)
    (hbd : ¬G.Adj b d) (hbe : ¬G.Adj b e) (hce : ¬G.Adj c e)
    (hae_ne : a ≠ e) :
    5 ≤ largestInducedPathSize G := by
  let f : Fin 5 → α := ![a, b, c, d, e]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let s : Finset α := Finset.univ.image f
  let qfun : Fin 5 → (s : Set α) := fun i => ⟨f i, by simp [s]⟩
  have hqfun_bij : Function.Bijective qfun := by
    refine ⟨fun i j hij => hf (congrArg Subtype.val hij), ?_⟩
    rintro ⟨x, hx⟩
    simp only [s, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨i, rfl⟩
  let q : Fin 5 ≃ (s : Set α) := Equiv.ofBijective qfun hqfun_bij
  have hqval (i : Fin 5) : (q i : α) = f i := by
    rfl
  have hba : G.Adj b a := hab.symm
  have hcb : G.Adj c b := hbc.symm
  have hdc : G.Adj d c := hcd.symm
  have hed : G.Adj e d := hde.symm
  have hca : ¬G.Adj c a := fun h => hac h.symm
  have hda : ¬G.Adj d a := fun h => had h.symm
  have hea : ¬G.Adj e a := fun h => hae h.symm
  have hdb : ¬G.Adj d b := fun h => hbd h.symm
  have heb : ¬G.Adj e b := fun h => hbe h.symm
  have hec : ¬G.Adj e c := fun h => hce h.symm
  let gi : pathGraph 5 ≃g G.induce (s : Set α) :=
    { toEquiv := q
      map_rel_iff' := by
        intro i j
        rw [induce_adj]
        simp only [hqval]
        fin_cases i <;> fin_cases j <;>
          simp_all [f, pathGraph_adj] }
  have htree : (G.induce (s : Set α)).IsTree := gi.isTree_iff.mp pathGraph_five_isTree
  have hdegree : ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 := by
    intro v
    obtain ⟨i, rfl⟩ := gi.surjective v
    rw [← degree_eq_of_iso gi i]
    exact pathGraph_five_degree_le_two i
  have hscard : s.card = 5 := by
    calc
      s.card = Finset.univ.card := Finset.card_image_of_injective _ hf
      _ = 5 := by simp
  unfold largestInducedPathSize
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro n ⟨t, rfl, _⟩
    exact Finset.card_le_univ t
  · exact ⟨s, hscard, htree, hdegree⟩

omit [Fintype α] [DecidableEq α] in
private lemma eq_snd_of_adj_mem_support_of_length_eq_dist {G : SimpleGraph α}
    {u v z : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    (hzp : z ∈ p.support) (huz : G.Adj u z) : z = p.snd := by
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hzp
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    exact huz.ne (by simpa using hi)
  have hi1 : i = 1 := by
    by_contra hi1
    have htwo : 2 ≤ i := by omega
    let q : G.Walk u v := (p.drop i).cons (hi ▸ huz)
    have hdist := G.dist_le q
    dsimp [q] at hdist
    rw [Walk.drop_length, ← hp] at hdist
    omega
  simpa [hi1] using hi.symm

private lemma dist_le_three_of_largestInducedPathSize_le_four
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hPath : largestInducedPathSize G ≤ 4) (u v : α) : G.dist u v ≤ 3 := by
  by_contra hdist
  have hfour : 4 ≤ G.dist u v := by omega
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  let q := p.take 4
  have hqlen : q.length = 4 := by simp [q, hp, Nat.min_eq_left hfour]
  have hqdist : q.length = G.dist u (p.getVert 4) :=
    length_eq_dist_of_subwalk hp (Walk.isSubwalk_take p 4)
  have hqpath := q.isPath_of_length_eq_dist hqdist
  have h01 : G.Adj (q.getVert 0) (q.getVert 1) := q.adj_getVert_succ (by omega)
  have h12 : G.Adj (q.getVert 1) (q.getVert 2) := q.adj_getVert_succ (by omega)
  have h23 : G.Adj (q.getVert 2) (q.getVert 3) := q.adj_getVert_succ (by omega)
  have h34 : G.Adj (q.getVert 3) (q.getVert 4) := q.adj_getVert_succ (by omega)
  have h0j : ∀ j, 2 ≤ j → j ≤ 4 → ¬G.Adj (q.getVert 0) (q.getVert j) := by
    intro j hj2 hj4 hadj
    have heq := eq_snd_of_adj_mem_support_of_length_eq_dist hqdist
      (q.getVert_mem_support j) (by simpa [q] using hadj)
    have hinj := hqpath.getVert_injOn
    have : j = 1 := hinj (by simp [hqlen]; omega) (by simp [hqlen]) heq
    omega
  have htaildist : (q.drop 1).length = G.dist (q.getVert 1) (p.getVert 4) :=
    length_eq_dist_of_subwalk hqdist (Walk.isSubwalk_drop q 1)
  have h1j : ∀ j, 3 ≤ j → j ≤ 4 → ¬G.Adj (q.getVert 1) (q.getVert j) := by
    intro j hj3 hj4 hadj
    have hj1 : 1 ≤ j := by omega
    have heq := eq_snd_of_adj_mem_support_of_length_eq_dist htaildist
      ((q.drop 1).getVert_mem_support (j - 1)) (by
        simpa [Walk.drop_getVert, Nat.add_sub_of_le hj1] using hadj)
    have hinj := hqpath.getVert_injOn
    have heq' : q.getVert j = q.getVert 2 := by
      simpa [Walk.drop_getVert, Nat.add_sub_of_le hj1] using heq
    have : j = 2 := hinj (by simp [hqlen]; omega) (by simp [hqlen]) heq'
    omega
  have htailtaildist : (q.drop 2).length = G.dist (q.getVert 2) (p.getVert 4) :=
    length_eq_dist_of_subwalk hqdist (Walk.isSubwalk_drop q 2)
  have h24 : ¬G.Adj (q.getVert 2) (q.getVert 4) := by
    intro hadj
    have heq := eq_snd_of_adj_mem_support_of_length_eq_dist htailtaildist
      ((q.drop 2).getVert_mem_support 2) (by simpa [Walk.drop_getVert] using hadj)
    have hinj := hqpath.getVert_injOn
    have heq' : q.getVert 4 = q.getVert 3 := by
      simpa [Walk.drop_getVert] using heq
    have : (4 : ℕ) = 3 := hinj (by simp [hqlen]) (by simp [hqlen]) heq'
    omega
  have h04ne : q.getVert 0 ≠ q.getVert 4 := by
    intro heq
    have : (0 : ℕ) = 4 := hqpath.getVert_injOn
      (by simp [hqlen]) (by simp [hqlen]) heq
    omega
  have := five_le_largestInducedPathSize_of_chordlessPath G h01 h12 h23 h34
    (h0j 2 (by omega) (by omega)) (h0j 3 (by omega) (by omega))
    (h0j 4 (by omega) (by omega)) (h1j 3 (by omega) (by omega))
    (h1j 4 (by omega) (by omega)) h24 h04ne
  omega

omit [Fintype α] in
private lemma exists_private_neighbor
    (G : SimpleGraph α) [DecidableRel G.Adj] {S : Finset α}
    (hS : IsMinimalTotalDominatingSet G S) {x : α} (hx : x ∈ S) :
    ∃ p : α, G.Adj p x ∧ ∀ y ∈ S, G.Adj p y → y = x := by
  have hnot : ¬IsTotalDominatingSet G (S.erase x) :=
    hS.2 (S.erase x) (Finset.erase_ssubset hx)
  unfold IsTotalDominatingSet at hnot
  push_neg at hnot
  obtain ⟨p, hp⟩ := hnot
  obtain ⟨y, hyS, hpy⟩ := hS.1 p
  have hyx : y = x := by
    by_contra hne
    exact hp y (Finset.mem_erase.mpr ⟨hne, hyS⟩) hpy
  subst y
  refine ⟨p, hpy, ?_⟩
  intro y hyS hpy'
  by_contra hne
  exact hp y (Finset.mem_erase.mpr ⟨hne, hyS⟩) hpy'

private lemma no_chordlessPath_four_in_minimal
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hPath : largestInducedPathSize G ≤ 4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {a b c d : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (_hac_ne : a ≠ c) (had_ne : a ≠ d) (hbd_ne : b ≠ d)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hbd : ¬G.Adj b d) : False := by
  obtain ⟨e, hed, hepriv⟩ := exists_private_neighbor G hS hd
  have hae : ¬G.Adj a e := by
    intro hae
    exact had_ne (hepriv a ha hae.symm)
  have hbe : ¬G.Adj b e := by
    intro hbe
    exact hbd_ne (hepriv b hb hbe.symm)
  have hce : ¬G.Adj c e := by
    intro hce
    exact hcd.ne (hepriv c hc hce.symm)
  have hae_ne : a ≠ e := by
    intro h
    subst e
    exact had hed
  have hlower := five_le_largestInducedPathSize_of_chordlessPath G
    hab hbc hcd hed.symm hac had hae hbd hbe hce hae_ne
  omega

omit [Fintype α] in
private lemma walk_exists_adj_mem_notMem {H : SimpleGraph α} {a b : α}
    (p : H.Walk a b) (s : Finset α) (ha : a ∈ s) (hb : b ∉ s) :
    ∃ x y : α, x ∈ s ∧ y ∉ s ∧ H.Adj x y := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a c b hac p ih =>
      by_cases hc : c ∈ s
      · exact ih hc hb
      · exact ⟨a, c, ha, hc, hac⟩

private lemma no_three_neighbors_in_minimal
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {a b c d : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d) : False := by
  obtain ⟨pb, hpb, hpbpriv⟩ := exists_private_neighbor G hS hb
  obtain ⟨pc, hpc, hpcpriv⟩ := exists_private_neighbor G hS hc
  obtain ⟨pd, hpd, hpdpriv⟩ := exists_private_neighbor G hS hd
  have hbc : ¬G.Adj b c := fun h => hTriFree b c a h hac.symm hab
  have hbd : ¬G.Adj b d := fun h => hTriFree b d a h had.symm hab
  have hcd : ¬G.Adj c d := fun h => hTriFree c d a h had.symm hac
  have make_path {u v pu pv : α}
      (hu : u ∈ S) (hv : v ∈ S) (hau : G.Adj a u) (hav : G.Adj a v)
      (huv : ¬G.Adj u v) (huv_ne : u ≠ v)
      (hpu : G.Adj pu u) (hpupriv : ∀ y ∈ S, G.Adj pu y → y = u)
      (hpv : G.Adj pv v) (hpvpriv : ∀ y ∈ S, G.Adj pv y → y = v)
      (hpupv : ¬G.Adj pu pv) : False := by
    have hpua : ¬G.Adj pu a := by
      intro h
      exact hau.ne (hpupriv a ha h)
    have hpuv : ¬G.Adj pu v := by
      intro h
      exact huv_ne (hpupriv v hv h).symm
    have hu_pv : ¬G.Adj u pv := by
      intro h
      exact huv_ne (hpvpriv u hu h.symm)
    have ha_pv : ¬G.Adj a pv := by
      intro h
      exact hav.ne (hpvpriv a ha h.symm)
    have hpupv_ne : pu ≠ pv := by
      intro h
      subst pv
      exact huv_ne (hpupriv v hv hpv).symm
    have hlower := five_le_largestInducedPathSize_of_chordlessPath G
      hpu hau.symm hav hpv.symm hpua hpuv hpupv huv hu_pv ha_pv hpupv_ne
    omega
  by_cases hpbc : G.Adj pb pc
  · by_cases hpbd : G.Adj pb pd
    · have hpcpd : ¬G.Adj pc pd := by
        intro h
        exact hTriFree pc pd pb h hpbd.symm hpbc
      exact make_path hc hd hac had hcd hcd_ne hpc hpcpriv hpd hpdpriv hpcpd
    · exact make_path hb hd hab had hbd hbd_ne hpb hpbpriv hpd hpdpriv hpbd
  · exact make_path hb hc hab hac hbc hbc_ne hpb hpbpriv hpc hpcpriv hpbc

private lemma no_four_cycle_in_minimal
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {a b c d : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : G.Adj a b) (hac : G.Adj a c) (hdb : G.Adj d b) (hdc : G.Adj d c)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (had_ne : a ≠ d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d) : False := by
  obtain ⟨pa, hpa, hpapriv⟩ := exists_private_neighbor G hS ha
  obtain ⟨pb, hpb, hpbpriv⟩ := exists_private_neighbor G hS hb
  obtain ⟨pd, hpd, hpdpriv⟩ := exists_private_neighbor G hS hd
  have had : ¬G.Adj a d := fun h => hTriFree a d b h hdb hab.symm
  have hbc : ¬G.Adj b c := fun h => hTriFree b c a h hac.symm hab
  have priv_nonadj {p x y : α} (hx : x ∈ S)
      (hp : ∀ z ∈ S, G.Adj p z → z = y) (hxy : x ≠ y) : ¬G.Adj p x := by
    intro h
    exact hxy (hp x hx h)
  have hpa_b := priv_nonadj hb hpapriv hab_ne.symm
  have hpa_c := priv_nonadj hc hpapriv hac_ne.symm
  have hpa_d := priv_nonadj hd hpapriv had_ne.symm
  have hpb_a := priv_nonadj ha hpbpriv hab_ne
  have hpb_c := priv_nonadj hc hpbpriv hbc_ne.symm
  have hpb_d := priv_nonadj hd hpbpriv hbd_ne.symm
  have hpd_a := priv_nonadj ha hpdpriv had_ne
  have hpd_b := priv_nonadj hb hpdpriv hbd_ne
  have hpd_c := priv_nonadj hc hpdpriv hcd_ne
  have hpb_c_ne : pb ≠ c := by
    intro h
    subst pb
    exact hbc hpb.symm
  by_cases hpapd : G.Adj pa pd
  · by_cases hpbpa : G.Adj pb pa
    · have hpbpd : ¬G.Adj pb pd := by
        intro h
        exact hTriFree pb pa pd hpbpa hpapd h.symm
      have hlower := five_le_largestInducedPathSize_of_chordlessPath G
        hpbpa hpapd hpd hdc hpbpd hpb_d hpb_c hpa_d hpa_c hpd_c hpb_c_ne
      omega
    · by_cases hpbpd : G.Adj pb pd
      · have hpbpa' : ¬G.Adj pb pa := hpbpa
        have hlower := five_le_largestInducedPathSize_of_chordlessPath G
          hpbpd hpapd.symm hpa hac hpbpa' hpb_a hpb_c hpd_a hpd_c hpa_c hpb_c_ne
        omega
      · have hpbpd_ne : pb ≠ pd := by
          intro h
          subst pd
          exact hbd_ne (hpdpriv b hb hpb)
        have hlower := five_le_largestInducedPathSize_of_chordlessPath G
          hpb hab.symm hpa.symm hpapd hpb_a hpbpa hpbpd
          (fun h => hpa_b h.symm) (fun h => hpd_b h.symm)
          (fun h => hpd_a h.symm) hpbpd_ne
        omega
  · have hpapd_ne : pa ≠ pd := by
      intro h
      subst pd
      exact had_ne (hpdpriv a ha hpa)
    have hlower := five_le_largestInducedPathSize_of_chordlessPath G
      hpa hab hdb.symm hpd.symm hpa_b hpa_d hpapd had
      (fun h => hpd_a h.symm) (fun h => hpd_b h.symm) hpapd_ne
    omega

private lemma card_le_three_of_minimal [Nonempty α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) : S.card ≤ 3 := by
  by_contra hcard
  have hfour : 4 ≤ S.card := by omega
  obtain ⟨v⟩ := ‹Nonempty α›
  obtain ⟨a, ha, _⟩ := hS.1 v
  obtain ⟨b, hb, hab⟩ := hS.1 a
  let H : SimpleGraph (S : Set α) := G.induce (S : Set α)
  let A : (S : Set α) := ⟨a, ha⟩
  let B : (S : Set α) := ⟨b, hb⟩
  have hAB : H.Adj A B := hab
  by_cases hHconn : H.Connected
  · let U : Finset (S : Set α) := H.neighborFinset A ∪ H.neighborFinset B
    have hAU : A ∈ U := by simp [U, hAB.symm]
    have hBU : B ∈ U := by simp [U, hAB]
    have hU : U = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro C
      by_contra hCU
      obtain ⟨p, _⟩ := hHconn.exists_isPath A C
      obtain ⟨X, Y, hXU, hYU, hXY⟩ :=
        walk_exists_adj_mem_notMem p U hAU hCU
      have hYA : ¬H.Adj A Y := by
        intro h
        exact hYU (by simp [U, h])
      have hYB : ¬H.Adj B Y := by
        intro h
        exact hYU (by simp [U, h])
      have hAY_ne : a ≠ Y.1 := by
        intro h
        apply hYU
        have hsub : A = Y := Subtype.ext h
        simpa [hsub] using hAU
      have hBY_ne : b ≠ Y.1 := by
        intro h
        apply hYU
        have hsub : B = Y := Subtype.ext h
        simpa [hsub] using hBU
      rcases (by simpa [U] using hXU : H.Adj A X ∨ H.Adj B X) with hAX | hBX
      · have hBXn : ¬G.Adj b X.1 := by
          intro h
          exact hTriFree b a X.1 hab.symm hAX h.symm
        have hBX_ne : b ≠ X.1 := by
          intro h
          have hsub : B = X := Subtype.ext h
          exact hYB (by simpa [hsub] using hXY)
        exact no_chordlessPath_four_in_minimal G hPath hS hb ha X.2 Y.2
          hab.symm hAX hXY hBX_ne hBY_ne hAY_ne hBXn hYB hYA
      · have hAXn : ¬G.Adj a X.1 := by
          intro h
          exact hTriFree a b X.1 hab hBX h.symm
        have hAX_ne : a ≠ X.1 := by
          intro h
          have hsub : A = X := Subtype.ext h
          exact hYA (by simpa [hsub] using hXY)
        exact no_chordlessPath_four_in_minimal G hPath hS ha hb X.2 Y.2
          hab hBX hXY hAX_ne hAY_ne hBY_ne hAXn hYA hYB
    let R : Finset α := (S.erase a).erase b
    have hRcard : 1 < R.card := by
      dsimp [R]
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.ne.symm, hb⟩),
        Finset.card_erase_of_mem ha]
      omega
    obtain ⟨c, d, hcR, hdR, hcd_ne⟩ := Finset.one_lt_card_iff.mp hRcard
    have hc : c ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hcR).2).2
    have hd : d ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hdR).2).2
    have hca_ne : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hcR).2).1
    have hcb_ne : c ≠ b := (Finset.mem_erase.mp hcR).1
    have hda_ne : d ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hdR).2).1
    have hdb_ne : d ≠ b := (Finset.mem_erase.mp hdR).1
    let C : (S : Set α) := ⟨c, hc⟩
    let D : (S : Set α) := ⟨d, hd⟩
    have hCU : C ∈ U := by rw [hU]; simp
    have hDU : D ∈ U := by rw [hU]; simp
    have hCadj : G.Adj a c ∨ G.Adj b c := by simpa [U, H, A, B, C] using hCU
    have hDadj : G.Adj a d ∨ G.Adj b d := by simpa [U, H, A, B, D] using hDU
    rcases hCadj with hac | hbc <;> rcases hDadj with had | hbd
    · exact no_three_neighbors_in_minimal G hTriFree hPath hS ha hb hc hd
        hab hac had hcb_ne.symm hdb_ne.symm hcd_ne
    · by_cases hcd : G.Adj c d
      · exact no_four_cycle_in_minimal G hTriFree hPath hS ha hb hc hd
          hab hac hbd.symm hcd.symm hab.ne hca_ne.symm
          hda_ne.symm hcb_ne.symm hdb_ne.symm hcd_ne
      · have hcb : ¬G.Adj c b := fun h => hTriFree c b a h hab.symm hac
        have had : ¬G.Adj a d := fun h => hTriFree a d b h hbd.symm hab.symm
        exact no_chordlessPath_four_in_minimal G hPath hS hc ha hb hd
          hac.symm hab hbd hcb_ne hcd_ne hda_ne.symm hcb hcd had
    · by_cases hcd : G.Adj c d
      · exact no_four_cycle_in_minimal G hTriFree hPath hS hb ha hc hd
          hab.symm hbc had.symm hcd.symm hab.ne.symm hcb_ne.symm
          hdb_ne.symm hca_ne.symm hda_ne.symm hcd_ne
      · have hca : ¬G.Adj c a := fun h => hTriFree c a b h hab hbc
        have hbd : ¬G.Adj b d := fun h => hTriFree b d a h had.symm hab
        exact no_chordlessPath_four_in_minimal G hPath hS hc hb ha hd
          hbc.symm hab.symm had hca_ne hcd_ne hdb_ne.symm hca hcd hbd
    · exact no_three_neighbors_in_minimal G hTriFree hPath hS hb ha hc hd
        hab.symm hbc hbd hca_ne.symm hda_ne.symm hcd_ne
  · have hnot : ∃ C : (S : Set α), ¬H.Reachable A C := by
      by_contra hall
      push_neg at hall
      exact hHconn (H.connected_iff_exists_forall_reachable.mpr ⟨A, hall⟩)
    obtain ⟨C, hACreach⟩ := hnot
    obtain ⟨d, hd, hCd⟩ := hS.1 C.1
    let D : (S : Set α) := ⟨d, hd⟩
    have hCD : H.Adj C D := hCd
    have hAC : ¬G.Adj a C.1 := fun h => hACreach (show H.Adj A C from h).reachable
    have hBC : ¬G.Adj b C.1 := by
      intro h
      exact hACreach (hAB.reachable.trans (show H.Adj B C from h).reachable)
    have hAD : ¬G.Adj a d := by
      intro h
      exact hACreach ((show H.Adj A D from h).reachable.trans hCD.symm.reachable)
    have hBD : ¬G.Adj b d := by
      intro h
      exact hACreach (hAB.reachable.trans
        ((show H.Adj B D from h).reachable.trans hCD.symm.reachable))
    have haC_ne : a ≠ C.1 := by
      intro h
      apply hACreach
      have hsub : A = C := Subtype.ext h
      exact hsub ▸ Reachable.rfl
    have hdistle := dist_le_three_of_largestInducedPathSize_le_four G hG hPath a C.1
    have hdistpos := hG.pos_dist_of_ne haC_ne
    have hdistneone : G.dist a C.1 ≠ 1 := by simpa using hAC
    have hdist : G.dist a C.1 = 2 ∨ G.dist a C.1 = 3 := by omega
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a C.1
    rcases hdist with hdist | hdist
    · have hplen : p.length = 2 := hp.trans hdist
      let x := p.getVert 1
      have hax : G.Adj a x := by
        simpa [x] using p.adj_getVert_succ (show 0 < p.length by omega)
      have hxC : G.Adj x C.1 := by
        have h := p.adj_getVert_succ (show 1 < p.length by omega)
        rw [show p.getVert 2 = C.1 by rw [← hplen, p.getVert_length]] at h
        simpa [x] using h
      have hbx : ¬G.Adj b x := fun h => hTriFree b a x hab.symm hax h.symm
      have hxd : ¬G.Adj x d := fun h => hTriFree x C.1 d hxC hCd h.symm
      have hbd_ne : b ≠ d := by
        intro h
        subst d
        exact hBC hCd.symm
      have hlower := five_le_largestInducedPathSize_of_chordlessPath G
        hab.symm hax hxC hCd hbx hBC hBD hAC hAD hxd hbd_ne
      omega
    · have hplen : p.length = 3 := hp.trans hdist
      let x := p.getVert 1
      let y := p.getVert 2
      have hax : G.Adj a x := by
        simpa [x] using p.adj_getVert_succ (show 0 < p.length by omega)
      have hxy : G.Adj x y := by
        simpa [x, y] using p.adj_getVert_succ (show 1 < p.length by omega)
      have hyC : G.Adj y C.1 := by
        have h := p.adj_getVert_succ (show 2 < p.length by omega)
        rw [show p.getVert 3 = C.1 by rw [← hplen, p.getVert_length]] at h
        simpa [y] using h
      have hbx : ¬G.Adj b x := fun h => hTriFree b a x hab.symm hax h.symm
      have hay : ¬G.Adj a y := fun h => hTriFree a x y hax hxy h.symm
      have hxd : ¬G.Adj x C.1 := fun h => hTriFree x y C.1 hxy hyC h.symm
      have hyd : ¬G.Adj y d := fun h => hTriFree y C.1 d hyC hCd h.symm
      by_cases hby : G.Adj b y
      · have had_ne : a ≠ d := by
          intro h
          subst d
          exact hAC hCd.symm
        have hlower := five_le_largestInducedPathSize_of_chordlessPath G
          hab hby hyC hCd hay hAC hAD hBC hBD hyd had_ne
        omega
      · have hbC_ne : b ≠ C.1 := by
          intro h
          apply hAC
          rw [← h]
          exact hab
        have hlower := five_le_largestInducedPathSize_of_chordlessPath G
          hab.symm hax hxy hyC hbx hby hBC hay hAC hxd hbC_ne
        omega

omit [Fintype α] in
private lemma two_le_card_of_totalDominating [Nonempty α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {S : Finset α}
    (hS : IsTotalDominatingSet G S) : 2 ≤ S.card := by
  obtain ⟨v⟩ := ‹Nonempty α›
  obtain ⟨w, hw, _⟩ := hS v
  obtain ⟨u, hu, hwu⟩ := hS w
  have hsub : {w, u} ⊆ S := by
    exact Finset.insert_subset_iff.mpr
      ⟨hw, Finset.singleton_subset_iff.mpr hu⟩
  have hcard := Finset.card_le_card hsub
  simpa [Finset.card_pair hwu.ne] using hcard

private lemma no_inducedPath_three_in_minimal_of_totalDominating_pair
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    {u v : α} (hpair : IsTotalDominatingSet G {u, v})
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {a b c : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac_ne : a ≠ c)
    (hac : ¬G.Adj a c) : False := by
  obtain ⟨p, hpa, hppriv⟩ := exists_private_neighbor G hS ha
  obtain ⟨q, hqc, hqpriv⟩ := exists_private_neighbor G hS hc
  have hdom (x : α) : G.Adj x u ∨ G.Adj x v := by
    obtain ⟨w, hw, hxw⟩ := hpair x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hxw
    · exact Or.inr hxw
  have hpq : ¬G.Adj p q := by
    rcases hdom a with hau | hav
    · have hpu : ¬G.Adj p u := fun h => hTriFree p a u hpa hau h.symm
      have hpv : G.Adj p v := (hdom p).resolve_left hpu
      have hbu : ¬G.Adj b u := fun h => hTriFree b a u hab.symm hau h.symm
      have hbv : G.Adj b v := (hdom b).resolve_left hbu
      have hcv : ¬G.Adj c v := fun h => hTriFree c b v hbc.symm hbv h.symm
      have hcu : G.Adj c u := (hdom c).resolve_right hcv
      have hqu : ¬G.Adj q u := fun h => hTriFree q c u hqc hcu h.symm
      have hqv : G.Adj q v := (hdom q).resolve_left hqu
      intro hpq
      exact hTriFree p v q hpv hqv.symm hpq.symm
    · have hpv : ¬G.Adj p v := fun h => hTriFree p a v hpa hav h.symm
      have hpu : G.Adj p u := (hdom p).resolve_right hpv
      have hbv : ¬G.Adj b v := fun h => hTriFree b a v hab.symm hav h.symm
      have hbu : G.Adj b u := (hdom b).resolve_right hbv
      have hcu : ¬G.Adj c u := fun h => hTriFree c b u hbc.symm hbu h.symm
      have hcv : G.Adj c v := (hdom c).resolve_left hcu
      have hqv : ¬G.Adj q v := fun h => hTriFree q c v hqc hcv h.symm
      have hqu : G.Adj q u := (hdom q).resolve_right hqv
      intro hpq
      exact hTriFree p u q hpu hqu.symm hpq.symm
  have hpb : ¬G.Adj p b := by
    intro h
    exact hab.ne (hppriv b hb h).symm
  have hpc : ¬G.Adj p c := by
    intro h
    exact hac_ne (hppriv c hc h).symm
  have haq : ¬G.Adj a q := by
    intro h
    exact hac_ne (hqpriv a ha h.symm)
  have hbq : ¬G.Adj b q := by
    intro h
    exact hbc.ne (hqpriv b hb h.symm)
  have hpq_ne : p ≠ q := by
    intro h
    subst q
    exact hac_ne (hppriv c hc hqc).symm
  have hlower := five_le_largestInducedPathSize_of_chordlessPath G
    hpa hab hbc hqc.symm hpb hpc hpq hac haq hbq hpq_ne
  omega

private lemma card_ne_three_of_minimal_of_totalDominating_pair
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    {u v : α} (hpair : IsTotalDominatingSet G {u, v})
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) : S.card ≠ 3 := by
  intro hcard
  obtain ⟨a, b, c, hab_ne, hac_ne, hbc_ne, hSset⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ S := by rw [hSset]; simp
  have hb : b ∈ S := by rw [hSset]; simp
  have hc : c ∈ S := by rw [hSset]; simp
  obtain ⟨w, hw, haw⟩ := hS.1 a
  have hwcases : w = a ∨ w = b ∨ w = c := by simpa [hSset] using hw
  rcases hwcases with hwa | hwb | hwc
  · subst w
    exact haw.ne rfl
  · subst w
    obtain ⟨z, hz, hcz⟩ := hS.1 c
    have hzcases : z = a ∨ z = b ∨ z = c := by simpa [hSset] using hz
    rcases hzcases with hza | hzb | hzc
    · subst z
      have hbc : ¬G.Adj b c := fun h => hTriFree b a c haw.symm hcz.symm h.symm
      exact no_inducedPath_three_in_minimal_of_totalDominating_pair G hTriFree hPath
        hpair hS hb ha hc haw.symm hcz.symm hbc_ne hbc
    · subst z
      have hac : ¬G.Adj a c := fun h => hTriFree a b c haw hcz.symm h.symm
      exact no_inducedPath_three_in_minimal_of_totalDominating_pair G hTriFree hPath
        hpair hS ha hb hc haw hcz.symm hac_ne hac
    · subst z
      exact hcz.ne rfl
  · subst w
    obtain ⟨z, hz, hbz⟩ := hS.1 b
    have hzcases : z = a ∨ z = b ∨ z = c := by simpa [hSset] using hz
    rcases hzcases with hza | hzb | hzc
    · subst z
      have hcb : ¬G.Adj c b := fun h => hTriFree c a b haw.symm hbz.symm h.symm
      exact no_inducedPath_three_in_minimal_of_totalDominating_pair G hTriFree hPath
        hpair hS hc ha hb haw.symm hbz.symm hbc_ne.symm hcb
    · subst z
      exact hbz.ne rfl
    · subst z
      have hab : ¬G.Adj a b := fun h => hTriFree a c b haw hbz.symm h.symm
      exact no_inducedPath_three_in_minimal_of_totalDominating_pair G hTriFree hPath
        hpair hS ha hc hb haw hbz.symm hab_ne hab

theorem conjecture314 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G := by
  intro S T hS hT
  have hSlo := two_le_card_of_totalDominating G hS.1
  have hTlo := two_le_card_of_totalDominating G hT.1
  have hShi := card_le_three_of_minimal G hG hTriFree hPath hS
  have hThi := card_le_three_of_minimal G hG hTriFree hPath hT
  by_cases hScard : S.card = 2
  · obtain ⟨u, v, huv, hSset⟩ := Finset.card_eq_two.mp hScard
    have hpair : IsTotalDominatingSet G {u, v} := by simpa [hSset] using hS.1
    have hTne := card_ne_three_of_minimal_of_totalDominating_pair
      G hTriFree hPath hpair hT
    omega
  · have hScard3 : S.card = 3 := by omega
    by_cases hTcard : T.card = 2
    · obtain ⟨u, v, huv, hTset⟩ := Finset.card_eq_two.mp hTcard
      have hpair : IsTotalDominatingSet G {u, v} := by simpa [hTset] using hT.1
      exact (card_ne_three_of_minimal_of_totalDominating_pair
        G hTriFree hPath hpair hS hScard3).elim
    · omega

end WrittenOnTheWallII.GraphConjecture314
