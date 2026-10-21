import Formal.Claude5E10Kill

/-!
# E10 model: the invariant along a literal path (`no_path_of_inv`)

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

theorem ev_map (f : ℤ × ℤ → ℤ × ℤ) (i : ℕ) (a b : ℤ × ℤ) :
    ev i (f a) (f b) = f (ev i a b) ∧ od i (f a) (f b) = f (od i a b) := by
  simp only [ev, od]; split_ifs <;> simp

theorem cross_gmap (c j : ℕ) (d z : ℤ × ℤ) :
    cross (rotN (gk c j) d) (gmap p r s w c j z) =
      cross d z + cross (rotN (gk c j) d) (gτ p r s w c j) := by
  simp only [gmap]; rw [cross_add', cross_rotN]

theorem ev_mem (i : ℕ) (b e : ℤ × ℤ) {P : ℤ × ℤ → Prop} (hb : P b) (he : P e) :
    P (ev i b e) ∧ P (od i b e) := by
  simp only [ev, od]; split_ifs <;> exact ⟨by assumption, by assumption⟩

section path

variable {n : ℕ} {q : ℕ → MS p r s}

theorem dom_cap {c : ℕ} (hc : c < 2) {z : ℤ × ℤ} (h : Dom p r s c z) : CapDom r s c z := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simpa [CapDom, Dom] using h

theorem unit_od_ev (i : ℕ) {b e : ℤ × ℤ} (h : e - b ∈ unitVec) :
    od (i + 1) b e - ev (i + 1) b e ∈ unitVec := by
  simp only [ev, od]; split_ifs
  · exact h
  · have := unit_neg h; simpa using this

theorem out_of {c j : ℕ} {d zE zO b : ℤ × ℤ} (hb : b = zE ∨ b = zO)
    (h : Out r s c j (b + d)) : Out r s c j (zE + d) ∨ Out r s c j (zO + d) := by
  rcases hb with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

theorem inn_of {c j : ℕ} {d zE zO b : ℤ × ℤ} (hb : b = zE ∨ b = zO)
    (h : Inn1 r s c j (b + d)) : Inn1 r s c j (zE + d) ∨ Inn1 r s c j (zO + d) := by
  rcases hb with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

theorem b_mem (i : ℕ) (b e : ℤ × ℤ) : b = ev (i + 1) b e ∨ b = od (i + 1) b e := by
  simp only [ev, od]; split_ifs <;> simp

/-- **One step of the invariant.** -/
theorem goodAt_succ (H : Hyp p r s w) (hq : LiteralPath (GM p r s w) n q)
    {G : ℕ → ℤ × ℤ → ℤ → ℤ → Prop} (hG : InvOK p r s w G) {i : ℕ} (hi : i + 3 < n)
    (hg : GoodAt p r s w G q i) : GoodAt p r s w G q (i + 1) := by
  obtain ⟨c, a, b, e, F, hgd⟩ := hg
  obtain ⟨en, on⟩ := ev_next i a b e
  have hc := F.1.1
  by_cases hd : Dom p r s c (b + e - a)
  · refine ⟨c, b, e, b + e - a, step_in H hq hi F hd, ?_⟩
    rw [show b + e - a - b = e - a by abel, en, on]; exact hgd
  have u3 := F.2.2.2.2.2
  have bm := b_mem i b e
  rcases c_cases hc with rfl | rfl | rfl
  · obtain ⟨j, hj, sb, se, so, F'⟩ := step_L H hq hi F (by simpa [Dom] using hd)
    refine ⟨2, _, _, _, F', ?_⟩
    rw [gmap_sub, show b + e - a - b = e - a by abel]
    obtain ⟨e1, e2⟩ := ev_map (gmap p r s w 0 j) (i + 1) b e
    rw [e1, e2, gmap_sub, cross_rotN, cross_gmap]
    obtain ⟨d1, d2⟩ := ev_mem (i + 1) b e (P := fun z => CapDom r s 0 z)
      (dom_cap (by norm_num) F.2.1.2.1) (dom_cap (by norm_num) F.2.2.1.2.1)
    obtain ⟨s1, s2⟩ := ev_mem (i + 1) b e (P := fun z => OnSide r s 0 j z) sb se
    have := hG.capT 0 j (by norm_num) hj (e - a) _ _ _ _ hgd d1 d2 s1 s2 (unit_od_ev i u3) en on
      (out_of bm (by rw [show b + (e - a) = b + e - a by abel]; exact so))
    rw [en, on]; exact this
  · obtain ⟨j, hj, sb, se, so, F'⟩ := step_U H hq hi F (by simpa [Dom] using hd)
    refine ⟨2, _, _, _, F', ?_⟩
    rw [gmap_sub, show b + e - a - b = e - a by abel]
    obtain ⟨e1, e2⟩ := ev_map (gmap p r s w 1 j) (i + 1) b e
    rw [e1, e2, gmap_sub, cross_rotN, cross_gmap]
    obtain ⟨d1, d2⟩ := ev_mem (i + 1) b e (P := fun z => CapDom r s 1 z)
      (dom_cap (by norm_num) F.2.1.2.1) (dom_cap (by norm_num) F.2.2.1.2.1)
    obtain ⟨s1, s2⟩ := ev_mem (i + 1) b e (P := fun z => OnSide r s 1 j z) sb se
    have := hG.capT 1 j (by norm_num) hj (e - a) _ _ _ _ hgd d1 d2 s1 s2 (unit_od_ev i u3) en on
      (out_of bm (by rw [show b + (e - a) = b + e - a by abel]; exact so))
    rw [en, on]; exact this
  · have hd' : ht (b + e - a) = -1 ∨ ht (b + e - a) = 2 * p + 1 := by
      obtain ⟨ha, hb, he, u1, u2, -⟩ := F
      have h1 := ht_unit u1; have h2 := ht_unit u2
      rw [ht_sub] at h1 h2
      have := ha.2.1; have := hb.2.1; have := he.2.1
      simp only [Dom, HT] at hd this
      simp only [Dom, HT, ht, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at *
      omega
    rcases hd' with hlow | hup
    · obtain ⟨j, t, zb, ze, hj, Hb, He, sb, se, gb, ge, iy, dy, F'⟩ := step_TL H hq hi F hlow
      refine ⟨0, zb, ze, _, F', ?_⟩
      set y := gmapInv p r s w 0 j (b + e - a + t • per r s)
      have hdy : rotN (gk 0 j) (y - zb) = e - a := by rw [dy]; abel
      have hE : cross (e - a) (ev i a b) = cross (rotN (gk 0 j) (y - zb))
          (gmap p r s w 0 j (ev (i + 1) zb ze) - t • per r s) := by
        obtain ⟨e1, -⟩ := ev_map (gmap p r s w 0 j) (i + 1) zb ze
        rw [hdy, ← e1, gb, ge]
        obtain ⟨e1', -⟩ := ev_map (fun z => z + t • per r s) (i + 1) b e
        beta_reduce at e1'
        rw [e1', add_sub_cancel_right, en]
      have hε : cross (y - zb) (od (i + 1) zb ze - ev (i + 1) zb ze) =
          cross (e - a) (od i a b - ev i a b) := by
        rw [← cross_rotN (gk 0 j), hdy, ← gmap_sub]
        obtain ⟨e1, e2⟩ := ev_map (gmap p r s w 0 j) (i + 1) zb ze
        rw [← e1, ← e2, gb, ge]
        obtain ⟨e1', e2'⟩ := ev_map (fun z => z + t • per r s) (i + 1) b e
        beta_reduce at e1' e2'
        rw [e1', e2', add_sub_add_right_eq_sub, on]
      have key := hG.Tcap 0 j (by norm_num) hj (y - zb) _ _ (ev (i + 1) zb ze) (od (i + 1) zb ze)
        t (by rw [hdy]; exact hgd) (ev_mem (i + 1) zb ze (P := fun z => CapDom r s 0 z)
          (by simpa [CapDom] using Hb) (by simpa [CapDom] using He)).1
        (ev_mem (i + 1) zb ze (P := fun z => CapDom r s 0 z)
          (by simpa [CapDom] using Hb) (by simpa [CapDom] using He)).2
        (ev_mem (i + 1) zb ze (P := fun z => OnSide r s 0 j z) sb se).1
        (ev_mem (i + 1) zb ze (P := fun z => OnSide r s 0 j z) sb se).2
        (unit_od_ev i (F'.2.2.2.1)) hE hε
        (inn_of (b_mem i zb ze) (by rw [show zb + (y - zb) = y by abel]; exact iy))
      rw [hε]; exact key
    · obtain ⟨j, t, zb, ze, hj, Hb, He, sb, se, gb, ge, iy, dy, F'⟩ := step_TU H hq hi F hup
      refine ⟨1, zb, ze, _, F', ?_⟩
      set y := gmapInv p r s w 1 j (b + e - a + t • per r s)
      have hdy : rotN (gk 1 j) (y - zb) = e - a := by rw [dy]; abel
      have hE : cross (e - a) (ev i a b) = cross (rotN (gk 1 j) (y - zb))
          (gmap p r s w 1 j (ev (i + 1) zb ze) - t • per r s) := by
        obtain ⟨e1, -⟩ := ev_map (gmap p r s w 1 j) (i + 1) zb ze
        rw [hdy, ← e1, gb, ge]
        obtain ⟨e1', -⟩ := ev_map (fun z => z + t • per r s) (i + 1) b e
        beta_reduce at e1'
        rw [e1', add_sub_cancel_right, en]
      have hε : cross (y - zb) (od (i + 1) zb ze - ev (i + 1) zb ze) =
          cross (e - a) (od i a b - ev i a b) := by
        rw [← cross_rotN (gk 1 j), hdy, ← gmap_sub]
        obtain ⟨e1, e2⟩ := ev_map (gmap p r s w 1 j) (i + 1) zb ze
        rw [← e1, ← e2, gb, ge]
        obtain ⟨e1', e2'⟩ := ev_map (fun z => z + t • per r s) (i + 1) b e
        beta_reduce at e1' e2'
        rw [e1', e2', add_sub_add_right_eq_sub, on]
      have key := hG.Tcap 1 j (by norm_num) hj (y - zb) _ _ (ev (i + 1) zb ze) (od (i + 1) zb ze)
        t (by rw [hdy]; exact hgd) (ev_mem (i + 1) zb ze (P := fun z => CapDom r s 1 z)
          (by simpa [CapDom] using Hb) (by simpa [CapDom] using He)).1
        (ev_mem (i + 1) zb ze (P := fun z => CapDom r s 1 z)
          (by simpa [CapDom] using Hb) (by simpa [CapDom] using He)).2
        (ev_mem (i + 1) zb ze (P := fun z => OnSide r s 1 j z) sb se).1
        (ev_mem (i + 1) zb ze (P := fun z => OnSide r s 1 j z) sb se).2
        (unit_od_ev i (F'.2.2.2.1)) hE hε
        (inn_of (b_mem i zb ze) (by rw [show zb + (y - zb) = y by abel]; exact iy))
      rw [hε]; exact key
/-- **A line-state invariant forbids literal paths.** -/
theorem no_path_of_inv (H : Hyp p r s w) {G : ℕ → ℤ × ℤ → ℤ → ℤ → Prop}
    (hG : InvOK p r s w G)
    (hdeg : ∀ v : MS p r s, deg (GM p r s w) v = 5 → IsCornerV p r s w v.1) :
    ¬ LiteralPath (GM p r s w) n q := by
  intro hq
  have hn := hq.1
  -- the start
  have g0 : GoodAt p r s w G q 0 := by
    have c0 := hdeg (q 0) hq.2.2.2.2.2.1
    obtain ⟨c, a, b, e, ha, hb, he, u1, u2, u3⟩ :=
      tri H (lp_adj1 hq (i := 0) (by omega)) (lp_adj2 hq (i := 0) (by omega))
        (lp_adj1 hq (i := 1) (by omega))
    refine ⟨c, a, b, e, ⟨ha, hb, he, u1, u2, u3⟩, ?_⟩
    simp only [ev, od, Nat.zero_mod, ite_true]
    exact hG.start c a b e ha.1 (corner_pos H ha c0) ha.2.1 hb.2.1 he.2.1 u1 u2 u3
  have gall : ∀ k, k + 2 < n → GoodAt p r s w G q k := by
    intro k
    induction k with
    | zero => intro _; exact g0
    | succ k ih => intro hk; exact goodAt_succ H hq hG (by omega) (ih (by omega))
  -- the end: index `n - 3` is odd
  obtain ⟨c, a, b, e, ⟨ha, hb, he, u1, u2, u3⟩, hgd⟩ := gall (n - 3) (by omega)
  have hodd : (n - 3) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hq.2.1; omega
  simp only [ev, od, hodd, show (1 : ℕ) ≠ 0 by norm_num, ite_false] at hgd
  have hlast : (q (n - 3 + 2)) = q (n - 1) := by congr 1; omega
  have cn := hdeg (q (n - 1)) hq.2.2.2.2.2.2.1
  rw [← hlast] at cn
  have cp := corner_pos H he cn
  apply hG.avoid c (e - a) _ _ e ha.1 hgd cp
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

end path

end Claude5E10
