import Formal.Claude5E10Three2
import Mathlib.Tactic.Abel

/-!
# E10 model: the twelve cap sides and their isometries to the tube

Written by a Claude worker (2026-10-20, E10 bridge session).

Side `i` of a cap runs from its corner `i` to corner `i + 1` (counterclockwise in cap
coordinates: lower `L0 … L5`, upper `U0 U5 U4 U3 U2 U1`).  The isometry `gmap c i` (rotation
`rotN (gk c i)` and translation `gτ c i`) carries the side onto the seam row of the tube
(`h = 0` below, `h = 2p` above) and the points one step outside the cap onto the row next to it
(`h = 1`, `h = 2p − 1`).

* `OnSide c i z`, `Out c i z`, `Inn1 c i z` : the line of side `i`, one step outside, one step
  inside;
* `gmap_ch` : on side `i`, `ch 2 (gmap c i z) = ch c z`;
* `gmap_out`, `gmapInv_in` : heights of the neighbouring rows.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- Height of a tube chart point. -/
def ht (z : ℤ × ℤ) : ℤ := z.1 + z.2

/-- Rotation exponent of the side isometry. -/
def gk : ℕ → ℕ → ℕ
  | 0, 0 => 2 | 0, 1 => 1 | 0, 2 => 0 | 0, 3 => 5 | 0, 4 => 4 | 0, _ => 3
  | _, 0 => 5 | _, 1 => 4 | _, 2 => 3 | _, 3 => 2 | _, 4 => 1 | _, _ => 0

/-- Translation of the side isometry. -/
def gτ (p r s w : ℤ) : ℕ → ℕ → ℤ × ℤ
  | 0, 0 => (3 * (2 * r + s), -(3 * (2 * r + s)))
  | 0, 1 => (3 * (2 * r + s) - r, -(3 * (2 * r + s)))
  | 0, 2 => (2 * (2 * r + s) - r, r - 3 * (2 * r + s))
  | 0, 3 => ((2 * r + s) - r, r - 2 * (2 * r + s))
  | 0, 4 => (0, r - (2 * r + s))
  | 0, _ => (0, 0)
  | _, 0 => (w, 2 * p - w)
  | _, 1 => (w + r + s, 2 * p - w)
  | _, 2 => (w + 3 * r + 2 * s, 2 * p - w - r - s)
  | _, 3 => (w + 3 * (2 * r + s) - r, 2 * p - w - 2 * (2 * r + s) + r)
  | _, 4 => (w + 3 * (2 * r + s), 2 * p - w - 3 * (2 * r + s) + r)
  | _, _ => (w + 3 * (2 * r + s), 2 * p - w - 3 * (2 * r + s))

/-- The side isometry. -/
def gmap (p r s w : ℤ) (c i : ℕ) (z : ℤ × ℤ) : ℤ × ℤ := rotN (gk c i) z + gτ p r s w c i

/-- Its inverse. -/
def gmapInv (p r s w : ℤ) (c i : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  rotN ((6 - gk c i) % 6) (z - gτ p r s w c i)

/-- The line of side `i`. -/
def OnSide (r s : ℤ) : ℕ → ℕ → ℤ × ℤ → Prop
  | 0, 0, z => z.2 = 0
  | 0, 1, z => z.1 = r
  | 0, 2, z => z.1 + z.2 = 2 * r + s
  | 0, 3, z => z.2 = 2 * r + s
  | 0, 4, z => z.1 = -(r + s)
  | 0, _, z => z.1 + z.2 = 0
  | _, 0, z => z.2 = 0
  | _, 1, z => z.1 = r + s
  | _, 2, z => z.1 + z.2 = 2 * r + s
  | _, 3, z => z.2 = 2 * r + s
  | _, 4, z => z.1 = -r
  | _, _, z => z.1 + z.2 = 0

/-- One step outside side `i`. -/
def Out (r s : ℤ) : ℕ → ℕ → ℤ × ℤ → Prop
  | 0, 0, z => z.2 = -1
  | 0, 1, z => z.1 = r + 1
  | 0, 2, z => z.1 + z.2 = 2 * r + s + 1
  | 0, 3, z => z.2 = 2 * r + s + 1
  | 0, 4, z => z.1 = -(r + s) - 1
  | 0, _, z => z.1 + z.2 = -1
  | _, 0, z => z.2 = -1
  | _, 1, z => z.1 = r + s + 1
  | _, 2, z => z.1 + z.2 = 2 * r + s + 1
  | _, 3, z => z.2 = 2 * r + s + 1
  | _, 4, z => z.1 = -r - 1
  | _, _, z => z.1 + z.2 = -1

/-- One step inside side `i`. -/
def Inn1 (r s : ℤ) : ℕ → ℕ → ℤ × ℤ → Prop
  | 0, 0, z => z.2 = 1
  | 0, 1, z => z.1 = r - 1
  | 0, 2, z => z.1 + z.2 = 2 * r + s - 1
  | 0, 3, z => z.2 = 2 * r + s - 1
  | 0, 4, z => z.1 = -(r + s) + 1
  | 0, _, z => z.1 + z.2 = 1
  | _, 0, z => z.2 = 1
  | _, 1, z => z.1 = r + s - 1
  | _, 2, z => z.1 + z.2 = 2 * r + s - 1
  | _, 3, z => z.2 = 2 * r + s - 1
  | _, 4, z => z.1 = -r + 1
  | _, _, z => z.1 + z.2 = 1

/-- The cap domain. -/
def CapDom (r s : ℤ) (c : ℕ) (z : ℤ × ℤ) : Prop := if c = 0 then HL r s z else HU r s z

theorem rotN_explicit (k : ℕ) (hk : k < 6) (z : ℤ × ℤ) : rotN k z =
    if k = 0 then z else if k = 1 then (-z.2, z.1 + z.2) else if k = 2 then (-z.1 - z.2, z.1)
    else if k = 3 then (-z.1, -z.2) else if k = 4 then (z.2, -z.1 - z.2) else (z.1 + z.2, -z.1) := by
  interval_cases k <;> simp [rotN, rot] <;> ring_nf

theorem rotN_sub' (k : ℕ) (z z' : ℤ × ℤ) : rotN k z - rotN k z' = rotN k (z - z') := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rotN, rot]
    rw [← ih]
    ext <;> simp <;> ring

theorem rotN_unit' (k : ℕ) {u : ℤ × ℤ} (h : u ∈ unitVec) : rotN k u ∈ unitVec := by
  induction k with
  | zero => exact h
  | succ k ih =>
    simp only [rotN]
    rw [unit_iff] at ih ⊢
    rcases ih with e | e | e | e | e | e <;> rw [e] <;> simp [rot]

theorem gmap_sub (c i : ℕ) (z z' : ℤ × ℤ) :
    gmap p r s w c i z - gmap p r s w c i z' = rotN (gk c i) (z - z') := by
  simp only [gmap]; rw [← rotN_sub']; abel

theorem gk_lt (c i : ℕ) : gk c i < 6 := by
  unfold gk; split <;> omega

theorem rotN_add' (m n : ℕ) (x : ℤ × ℤ) : rotN (m + n) x = rotN m (rotN n x) := by
  induction m with
  | zero => simp [rotN]
  | succ m ih => rw [show m + 1 + n = (m + n) + 1 by omega]; simp only [rotN, ih]

theorem rotN_six_mul' (q : ℕ) (x : ℤ × ℤ) : rotN (6 * q) x = x := by
  induction q with
  | zero => simp [rotN]
  | succ q ih =>
    rw [show 6 * (q + 1) = 6 + 6 * q by ring, rotN_add', ih]
    ext <;> simp [rotN, rot]

theorem rotN_mod6 (n : ℕ) (x : ℤ × ℤ) : rotN n x = rotN (n % 6) x := by
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [rotN_add', rotN_six_mul']

theorem rotN_add_mod (a b : ℕ) (z : ℤ × ℤ) : rotN a (rotN b z) = rotN ((a + b) % 6) z := by
  rw [← rotN_add' a b, rotN_mod6]

theorem gmap_inv (c i : ℕ) (z : ℤ × ℤ) : gmap p r s w c i (gmapInv p r s w c i z) = z := by
  simp only [gmap, gmapInv]
  rw [rotN_add_mod]
  have := gk_lt c i
  rw [show (gk c i + (6 - gk c i) % 6) % 6 = 0 by omega]
  simp [rotN]

theorem gmapInv_sub (c i : ℕ) (z z' : ℤ × ℤ) :
    gmapInv p r s w c i z - gmapInv p r s w c i z' = rotN ((6 - gk c i) % 6) (z - z') := by
  simp only [gmapInv]; rw [rotN_sub']; congr 1; abel

/-! ## The isometries on the sides -/

theorem emod_self_add {P x : ℤ} (hP : 0 < P) (h0 : 0 ≤ x) (h1 : x < P) : (x + P) % P = x := by
  rw [Int.add_emod_right, Int.emod_eq_of_lt h0 h1]

/-- On side `i` of the lower cap, the isometry gives the same vertex. -/
theorem gmapL_ch (H : Hyp p r s w) {i : ℕ} (hi : i < 6) {z : ℤ × ℤ} (hz : HL r s z)
    (hs : OnSide r s 0 i z) :
    ch p r s w 2 (gmap p r s w 0 i z) = ch p r s w 0 z ∧ ht (gmap p r s w 0 i z) = 0 := by
  have hr := H.hr; have hs' := H.hs
  have hP : 0 < 3 * (2 * r + s) := by omega
  have hb : ¬ IL r s z := by
    simp only [IL]; interval_cases i <;> simp only [OnSide] at hs <;> omega
  have key : ht (gmap p r s w 0 i z) = 0 ∧
      (gmap p r s w 0 i z).1 % (3 * (2 * r + s)) = aL r s z := by
    obtain ⟨x, y⟩ := z
    simp only [HL] at hz
    interval_cases i <;> simp only [OnSide] at hs <;>
      simp only [gmap, gk, gτ, ht, rotN, rot, Prod.fst_add, Prod.snd_add] <;>
      refine ⟨by omega, ?_⟩ <;> simp only [aL] <;> split_ifs <;>
      first
      | exact emod_eq_of hP (q := 0) (by omega) (by omega) (by omega)
      | exact emod_eq_of hP (q := 1) (by omega) (by omega) (by omega)
  refine ⟨?_, key.1⟩
  rw [chL_B hb, chT, key.2]
  simp only [ht] at key
  rw [key.1]

/-- On side `i` of the upper cap, the isometry gives the same vertex. -/
theorem gmapU_ch (H : Hyp p r s w) {i : ℕ} (hi : i < 6) {z : ℤ × ℤ} (hz : HU r s z)
    (hs : OnSide r s 1 i z) :
    ch p r s w 2 (gmap p r s w 1 i z) = ch p r s w 1 z ∧ ht (gmap p r s w 1 i z) = 2 * p := by
  have hr := H.hr; have hs' := H.hs; have := H.hw0; have := H.hw1
  have hP : 0 < 3 * (2 * r + s) := by omega
  have hb : ¬ IU r s z := by
    simp only [IU]; interval_cases i <;> simp only [OnSide] at hs <;> omega
  have key : ht (gmap p r s w 1 i z) = 2 * p ∧
      (gmap p r s w 1 i z).1 % (3 * (2 * r + s)) = wrap r s (aU r s z + w) := by
    obtain ⟨x, y⟩ := z
    simp only [HU] at hz
    interval_cases i <;> simp only [OnSide] at hs <;>
      simp only [gmap, gk, gτ, ht, rotN, rot, Prod.fst_add, Prod.snd_add] <;>
      refine ⟨by omega, ?_⟩ <;> simp only [aU, wrap] <;> split_ifs <;>
      first
      | exact emod_eq_of hP (q := 0) (by omega) (by omega) (by omega)
      | exact emod_eq_of hP (q := 1) (by omega) (by omega) (by omega)
      | (exfalso; omega)
  refine ⟨?_, key.1⟩
  rw [chU_B hb, chT, key.2]
  simp only [ht] at key
  rw [key.1]

/-- Heights of the side images: the side line, one step outside, one step inside. -/
theorem ht_gmapL {i : ℕ} (hi : i < 6) (z : ℤ × ℤ) :
    (OnSide r s 0 i z ↔ ht (gmap p r s w 0 i z) = 0) ∧
      (Out r s 0 i z ↔ ht (gmap p r s w 0 i z) = 1) ∧
        (Inn1 r s 0 i z ↔ ht (gmap p r s w 0 i z) = -1) := by
  obtain ⟨x, y⟩ := z
  interval_cases i <;> simp only [OnSide, Out, Inn1, gmap, gk, gτ, ht, rotN, rot,
    Prod.fst_add, Prod.snd_add] <;> omega

theorem ht_gmapU {i : ℕ} (hi : i < 6) (z : ℤ × ℤ) :
    (OnSide r s 1 i z ↔ ht (gmap p r s w 1 i z) = 2 * p) ∧
      (Out r s 1 i z ↔ ht (gmap p r s w 1 i z) = 2 * p - 1) ∧
        (Inn1 r s 1 i z ↔ ht (gmap p r s w 1 i z) = 2 * p + 1) := by
  obtain ⟨x, y⟩ := z
  interval_cases i <;> simp only [OnSide, Out, Inn1, gmap, gk, gτ, ht, rotN, rot,
    Prod.fst_add, Prod.snd_add] <;> omega

/-- A unit triangle of a cap whose third apex leaves the cap: the edge is on a side. -/
theorem exitL {a b e : ℤ × ℤ} (ha : HL r s a) (hb : HL r s b) (he : HL r s e)
    (h1 : b - a ∈ unitVec) (h2 : e - a ∈ unitVec) (h3 : e - b ∈ unitVec)
    (hn : ¬ HL r s (b + e - a)) :
    ∃ i, i < 6 ∧ OnSide r s 0 i b ∧ OnSide r s 0 i e ∧ Out r s 0 i (b + e - a) ∧
      Inn1 r s 0 i a := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨e1, e2⟩ := e
  rw [unit_sub] at h1 h2 h3
  simp only [U2] at h1 h2 h3
  simp only [HL, Prod.mk_add_mk, Prod.mk_sub_mk] at ha hb he hn
  simp only [OnSide, Out, Inn1, Prod.mk_add_mk, Prod.mk_sub_mk]
  by_cases c0 : b2 + e2 - a2 < 0
  · exact ⟨0, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  by_cases c1 : b1 + e1 - a1 > r
  · exact ⟨1, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  by_cases c2 : b1 + e1 - a1 + (b2 + e2 - a2) > 2 * r + s
  · exact ⟨2, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  by_cases c3 : b2 + e2 - a2 > 2 * r + s
  · exact ⟨3, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  by_cases c4 : b1 + e1 - a1 < -(r + s)
  · exact ⟨4, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  · exact ⟨5, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩

theorem exitU {a b e : ℤ × ℤ} (ha : HU r s a) (hb : HU r s b) (he : HU r s e)
    (h1 : b - a ∈ unitVec) (h2 : e - a ∈ unitVec) (h3 : e - b ∈ unitVec)
    (hn : ¬ HU r s (b + e - a)) :
    ∃ i, i < 6 ∧ OnSide r s 1 i b ∧ OnSide r s 1 i e ∧ Out r s 1 i (b + e - a) ∧
      Inn1 r s 1 i a := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨e1, e2⟩ := e
  rw [unit_sub] at h1 h2 h3
  simp only [U2] at h1 h2 h3
  simp only [HU, Prod.mk_add_mk, Prod.mk_sub_mk] at ha hb he hn
  simp only [OnSide, Out, Inn1, Prod.mk_add_mk, Prod.mk_sub_mk]
  by_cases c0 : b2 + e2 - a2 < 0
  · exact ⟨0, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  by_cases c1 : b1 + e1 - a1 > r + s
  · exact ⟨1, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  by_cases c2 : b1 + e1 - a1 + (b2 + e2 - a2) > 2 * r + s
  · exact ⟨2, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  by_cases c3 : b2 + e2 - a2 > 2 * r + s
  · exact ⟨3, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  by_cases c4 : b1 + e1 - a1 < -r
  · exact ⟨4, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩
  · exact ⟨5, by norm_num, by simp only [OnSide]; omega, by simp only [OnSide]; omega, by simp only [Out]; omega, by simp only [Inn1]; omega⟩

end Claude5E10
