import Formal.Claude5E10Two
import Formal.Claude5E10Deg4

/-!
# E10 as a Theorem 1a signature: the integer facts

Written by a Claude worker (2026-10-21, E10 bridge session).

The signature (built in `Claude5E10SigDef`) has five charts: `0` the lower cap `HL`, `1` the
upper cap `HU`, `2, 3, 4` the tube sectors `c m ≤ x ≤ (c + 1) m` of the tube strip.  It has 75
records: `0, 1` glue sector `c` to sector `c + 1` along `x = (c + 1) m`, `2` glues sector 2 to
sector 0 along `x = 3m` by `- per`, and `3 + 36 cap + 6 i + 2 c + e` maps the cap `cap` by the
side isometry `gmap cap i` minus `e` periods into sector `c`.

* `rec_sound` : a record identifies only points of one model vertex;
* `cap_rec` : every boundary point of a cap is carried by a record into a sector;
* `tube_cases` : two sector points of one model vertex are equal or joined by a record;
* `sec_inj` : `ch` is injective on one sector;
* `tube_place` : a run of two columns of the strip fits in one sector after a period shift.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- The model chart of a signature chart. -/
def qc (f : ℕ) : ℕ := if f < 2 then f else 2

/-- The signature chart domains. -/
def QD (p r s : ℤ) : ℕ → ℤ × ℤ → Prop
  | 0, z => HL r s z
  | 1, z => HU r s z
  | 2, z => 0 ≤ z.1 ∧ z.1 ≤ 2 * r + s ∧ HT p z
  | 3, z => 2 * r + s ≤ z.1 ∧ z.1 ≤ 2 * (2 * r + s) ∧ HT p z
  | _, z => 2 * (2 * r + s) ≤ z.1 ∧ z.1 ≤ 3 * (2 * r + s) ∧ HT p z

/-- Source chart of a record. -/
def rsrc (n : ℕ) : ℕ := if n = 0 then 2 else if n = 1 then 3 else if n = 2 then 4 else (n - 3) / 36

/-- Target chart of a record. -/
def rtgt (n : ℕ) : ℕ :=
  if n = 0 then 3 else if n = 1 then 4 else if n = 2 then 2 else 2 + (n - 3) / 2 % 3

/-- The map of a record. -/
def recMap (p r s w : ℤ) (n : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  if n < 2 then z else if n = 2 then z - per r s else
    gmap p r s w ((n - 3) / 36) ((n - 3) / 6 % 6) z - (((n - 3) % 2 : ℕ) : ℤ) • per r s

theorem qd_ht {f : ℕ} (hf : 2 ≤ f) {z : ℤ × ℤ} (h : QD p r s f z) : HT p z := by
  match f, hf with
  | 2, _ => exact h.2.2
  | 3, _ => exact h.2.2
  | f + 4, _ => exact h.2.2

theorem qc_lt (f : ℕ) : qc f < 3 := by unfold qc; split_ifs <;> omega

theorem dom_qd {f : ℕ} {z : ℤ × ℤ} (h : QD p r s f z) : Dom p r s (qc f) z := by
  match f with
  | 0 => exact h
  | 1 => exact h
  | f + 2 =>
    have : qc (f + 2) = 2 := by unfold qc; split_ifs <;> omega
    rw [this]; exact qd_ht (by omega) h

theorem ht_shift (y : ℤ × ℤ) (t : ℤ) : ht (y - t • per r s) = ht y := by
  simp only [ht, per, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]; ring

theorem chT_sub (y : ℤ × ℤ) (t : ℤ) : ch p r s w 2 (y - t • per r s) = ch p r s w 2 y := by
  have e : y - t • per r s = y + (-t) • per r s := by
    ext <;> simp [per] <;> ring
  rw [e, chT_shift]

theorem htL_nonpos {i : ℕ} (hi : i < 6) {z : ℤ × ℤ} (hz : HL r s z) :
    ht (gmap p r s w 0 i z) ≤ 0 := by
  obtain ⟨x, y⟩ := z
  simp only [HL] at hz
  interval_cases i <;> simp only [gmap, gk, gτ, ht, rotN, rot, Prod.fst_add, Prod.snd_add] <;>
    omega

theorem htU_ge {i : ℕ} (hi : i < 6) {z : ℤ × ℤ} (hz : HU r s z) :
    2 * p ≤ ht (gmap p r s w 1 i z) := by
  obtain ⟨x, y⟩ := z
  simp only [HU] at hz
  interval_cases i <;> simp only [gmap, gk, gτ, ht, rotN, rot, Prod.fst_add, Prod.snd_add] <;>
    omega

theorem gmapL_x (H : Hyp p r s w) {i : ℕ} (hi : i < 6) {z : ℤ × ℤ} (hz : HL r s z)
    (hs : OnSide r s 0 i z) :
    0 ≤ (gmap p r s w 0 i z).1 ∧ (gmap p r s w 0 i z).1 < 6 * (2 * r + s) := by
  have := H.hr; have := H.hs
  obtain ⟨x, y⟩ := z
  simp only [HL] at hz
  interval_cases i <;> simp only [OnSide] at hs <;>
    simp only [gmap, gk, gτ, rotN, rot, Prod.fst_add] <;> omega

theorem gmapU_x (H : Hyp p r s w) {i : ℕ} (hi : i < 6) {z : ℤ × ℤ} (hz : HU r s z)
    (hs : OnSide r s 1 i z) :
    0 ≤ (gmap p r s w 1 i z).1 ∧ (gmap p r s w 1 i z).1 < 6 * (2 * r + s) := by
  have := H.hr; have := H.hs; have := H.hw0; have := H.hw1
  obtain ⟨x, y⟩ := z
  simp only [HU] at hz
  interval_cases i <;> simp only [OnSide] at hs <;>
    simp only [gmap, gk, gτ, rotN, rot, Prod.fst_add] <;> omega

/-- The decoding of a cap record. -/
theorem rec_pick {cap i c e : ℕ} (hc : cap < 2) (hi : i < 6) (hc3 : c < 3) (he : e < 2)
    (z : ℤ × ℤ) :
    3 + cap * 36 + i * 6 + c * 2 + e < 75 ∧ rsrc (3 + cap * 36 + i * 6 + c * 2 + e) = cap ∧
      rtgt (3 + cap * 36 + i * 6 + c * 2 + e) = 2 + c ∧
      recMap p r s w (3 + cap * 36 + i * 6 + c * 2 + e) z = gmap p r s w cap i z - (e : ℤ) • per r s := by
  have d1 : (3 + cap * 36 + i * 6 + c * 2 + e - 3) / 36 = cap := by omega
  have d2 : (3 + cap * 36 + i * 6 + c * 2 + e - 3) / 6 % 6 = i := by omega
  have d3 : (3 + cap * 36 + i * 6 + c * 2 + e - 3) / 2 % 3 = c := by omega
  have d4 : (3 + cap * 36 + i * 6 + c * 2 + e - 3) % 2 = e := by omega
  refine ⟨by omega, ?_, ?_, ?_⟩
  · unfold rsrc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), d1]
  · unfold rtgt; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), d3]
  · unfold recMap; rw [if_neg (by omega), if_neg (by omega), d1, d2, d4]

/-- The data of a cap record. -/
theorem rec_data {n : ℕ} (hn : n < 75) (h3 : 3 ≤ n) :
    ∃ cap i c e : ℕ, cap < 2 ∧ i < 6 ∧ c < 3 ∧ e < 2 ∧ n = 3 + cap * 36 + i * 6 + c * 2 + e :=
  ⟨(n - 3) / 36, (n - 3) / 6 % 6, (n - 3) / 2 % 3, (n - 3) % 2, by omega, by omega, by omega,
    by omega, by omega⟩

/-- A point of a sector `2 + c`, by components. -/
theorem qd_sec {c : ℕ} (hc : c < 3) {y : ℤ × ℤ} :
    QD p r s (2 + c) y ↔ (c : ℤ) * (2 * r + s) ≤ y.1 ∧ y.1 ≤ ((c : ℤ) + 1) * (2 * r + s) ∧
      HT p y := by
  interval_cases c <;> simp only [QD] <;> push_cast <;> constructor <;> intro h <;>
    obtain ⟨a, b, d⟩ := h <;> exact ⟨by linarith, by linarith, d⟩

/-- **Records are sound.** -/
theorem rec_sound (H : Hyp p r s w) {n : ℕ} (hn : n < 75) {z : ℤ × ℤ}
    (h1 : QD p r s (rsrc n) z) (h2 : QD p r s (rtgt n) (recMap p r s w n z)) :
    ch p r s w (qc (rsrc n)) z = ch p r s w (qc (rtgt n)) (recMap p r s w n z) := by
  by_cases h3 : n < 3
  · have e1 : qc (rsrc n) = 2 := by unfold qc rsrc; split_ifs <;> omega
    have e2 : qc (rtgt n) = 2 := by unfold qc rtgt; split_ifs <;> omega
    rw [e1, e2]
    unfold recMap
    split_ifs with a b
    · rfl
    · rw [show z - per r s = z - (1 : ℤ) • per r s by simp, chT_sub]
    · omega
  obtain ⟨cap, i, c, e, hc, hi, hc3, he, rfl⟩ := rec_data hn (by omega)
  obtain ⟨-, d1, d2, d3⟩ := rec_pick (p := p) (r := r) (s := s) (w := w) hc hi hc3 he z
  rw [d1] at h1 ⊢
  rw [d2] at h2 ⊢
  rw [d3] at h2 ⊢
  have e2 : qc (2 + c) = 2 := by unfold qc; split_ifs <;> omega
  have e1 : qc cap = cap := by unfold qc; split_ifs <;> omega
  rw [e1, e2, chT_sub]
  have hT := qd_ht (by omega) h2
  simp only [HT] at hT
  have hh := ht_shift (r := r) (s := s) (gmap p r s w cap i z) (e : ℤ)
  simp only [ht] at hh
  rcases (show cap = 0 ∨ cap = 1 by omega) with rfl | rfl
  · have a := htL_nonpos (p := p) (w := w) hi h1
    simp only [ht] at a
    have hon := ((ht_gmapL (p := p) (w := w) hi z).1).2 (by simp only [ht]; linarith)
    exact (gmapL_ch H hi h1 hon).1.symm
  · have a := htU_ge (p := p) (w := w) hi h1
    simp only [ht] at a
    have hon := ((ht_gmapU (p := p) (w := w) hi z).1).2 (by simp only [ht]; linarith)
    exact (gmapU_ch H hi h1 hon).1.symm

/-- A side through a boundary point. -/
theorem side_of_bd {cap : ℕ} (hc : cap < 2) {z : ℤ × ℤ} (hz : QD p r s cap z)
    (hb : ch p r s w cap z ≠ ((cap : ℤ), z)) : ∃ i, i < 6 ∧ OnSide r s cap i z := by
  rcases (show cap = 0 ∨ cap = 1 by omega) with rfl | rfl
  · have hb' : ¬ IL r s z := fun h => hb (chL_I h)
    rcases bdL_cases hz hb' with h | h | h | h | h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
    · exact ⟨2, by omega, h⟩
    · exact ⟨3, by omega, h⟩
    · exact ⟨4, by omega, h⟩
    · exact ⟨5, by omega, h⟩
  · have hb' : ¬ IU r s z := fun h => hb (chU_I h)
    rcases bdU_cases hz hb' with h | h | h | h | h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
    · exact ⟨2, by omega, h⟩
    · exact ⟨3, by omega, h⟩
    · exact ⟨4, by omega, h⟩
    · exact ⟨5, by omega, h⟩

/-- A point of the strip with `0 ≤ x < 6m` lies in a sector after `e ∈ {0, 1}` periods. -/
theorem strip_sec (hr : 1 ≤ r) (hs : 1 ≤ s) {y : ℤ × ℤ} (hy : HT p y) (h0 : 0 ≤ y.1)
    (h1 : y.1 < 6 * (2 * r + s)) :
    ∃ c e : ℕ, c < 3 ∧ e < 2 ∧ QD p r s (2 + c) (y - (e : ℤ) • per r s) := by
  have hT : ∀ t : ℤ, HT p (y - t • per r s) := by
    intro t; simp only [HT, per, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul] at hy ⊢
    constructor <;> linarith [hy.1, hy.2]
  have hx : ∀ t : ℤ, (y - t • per r s).1 = y.1 - t * (3 * (2 * r + s)) := by
    intro t; simp [per]
  rcases (show y.1 < 2 * r + s ∨ (2 * r + s ≤ y.1 ∧ y.1 < 2 * (2 * r + s)) ∨
      (2 * (2 * r + s) ≤ y.1 ∧ y.1 < 3 * (2 * r + s)) ∨
      (3 * (2 * r + s) ≤ y.1 ∧ y.1 < 4 * (2 * r + s)) ∨
      (4 * (2 * r + s) ≤ y.1 ∧ y.1 < 5 * (2 * r + s)) ∨ 5 * (2 * r + s) ≤ y.1 by omega)
    with h | h | h | h | h | h
  · refine ⟨0, 0, by omega, by omega, (qd_sec (by omega)).2 ⟨?_, ?_, hT _⟩⟩ <;> rw [hx] <;>
      push_cast <;> linarith
  · refine ⟨1, 0, by omega, by omega, (qd_sec (by omega)).2 ⟨?_, ?_, hT _⟩⟩ <;> rw [hx] <;>
      push_cast <;> linarith
  · refine ⟨2, 0, by omega, by omega, (qd_sec (by omega)).2 ⟨?_, ?_, hT _⟩⟩ <;> rw [hx] <;>
      push_cast <;> linarith
  · refine ⟨0, 1, by omega, by omega, (qd_sec (by omega)).2 ⟨?_, ?_, hT _⟩⟩ <;> rw [hx] <;>
      push_cast <;> linarith
  · refine ⟨1, 1, by omega, by omega, (qd_sec (by omega)).2 ⟨?_, ?_, hT _⟩⟩ <;> rw [hx] <;>
      push_cast <;> linarith
  · refine ⟨2, 1, by omega, by omega, (qd_sec (by omega)).2 ⟨?_, ?_, hT _⟩⟩ <;> rw [hx] <;>
      push_cast <;> linarith

/-- **Every cap boundary point is carried into a sector.** -/
theorem cap_rec (H : Hyp p r s w) {cap : ℕ} (hc : cap < 2) {z : ℤ × ℤ} (hz : QD p r s cap z)
    (hb : ch p r s w cap z ≠ ((cap : ℤ), z)) :
    ∃ n, n < 75 ∧ rsrc n = cap ∧ 2 ≤ rtgt n ∧ QD p r s (rtgt n) (recMap p r s w n z) := by
  have hr := H.hr; have hs := H.hs; have hp := H.hp
  obtain ⟨i, hi, hon⟩ := side_of_bd hc hz hb
  have key : HT p (gmap p r s w cap i z) ∧ 0 ≤ (gmap p r s w cap i z).1 ∧
      (gmap p r s w cap i z).1 < 6 * (2 * r + s) := by
    rcases (show cap = 0 ∨ cap = 1 by omega) with rfl | rfl
    · have a := (gmapL_ch H hi hz hon).2
      simp only [ht] at a
      exact ⟨⟨by omega, by omega⟩, gmapL_x H hi hz hon⟩
    · have a := (gmapU_ch H hi hz hon).2
      simp only [ht] at a
      exact ⟨⟨by omega, by omega⟩, gmapU_x H hi hz hon⟩
  obtain ⟨c, e, hc3, he, hq⟩ := strip_sec hr hs key.1 key.2.1 key.2.2
  obtain ⟨d0, d1, d2, d3⟩ := rec_pick (p := p) (r := r) (s := s) (w := w) hc hi hc3 he z
  exact ⟨_, d0, d1, by omega, by rw [d2, d3]; exact hq⟩

/-- A small multiple of a positive number is `-1`, `0` or `1`. -/
theorem small_mul {t M : ℤ} (hM : 0 < M) (h1 : -M ≤ t * M) (h2 : t * M ≤ M) :
    t = -1 ∨ t = 0 ∨ t = 1 := by
  rcases (show t ≤ -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ 2 ≤ t by omega) with h | h | h | h | h
  · nlinarith
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · nlinarith

/-- **Two sector points of one model vertex.** -/
theorem tube_cases (hr : 1 ≤ r) (hs : 1 ≤ s) {f f' : ℕ} (hf : 2 ≤ f) (hf' : 2 ≤ f')
    (hf5 : f < 5) (hf5' : f' < 5) {z z' : ℤ × ℤ}
    (hz : QD p r s f z) (hz' : QD p r s f' z') (h : ch p r s w 2 z = ch p r s w 2 z') :
    (f = f' ∧ z = z') ∨ ∃ n, n < 3 ∧ ((rsrc n = f ∧ rtgt n = f' ∧ recMap p r s w n z = z') ∨
      (rsrc n = f' ∧ rtgt n = f ∧ recMap p r s w n z' = z)) := by
  obtain ⟨t, rfl⟩ := chT_rep hr hs h
  have ex : (z + t • per r s).1 = z.1 + t * (3 * (2 * r + s)) := by simp [per]
  have hm : 0 < 3 * (2 * r + s) := by omega
  -- the sector ranges
  obtain ⟨c, hc, rfl⟩ : ∃ c, c < 3 ∧ f = 2 + c := ⟨f - 2, by omega, by omega⟩
  obtain ⟨c', hc', rfl⟩ : ∃ c, c < 3 ∧ f' = 2 + c := ⟨f' - 2, by omega, by omega⟩
  obtain ⟨a1, a2, -⟩ := (qd_sec hc).1 hz
  obtain ⟨b1, b2, -⟩ := (qd_sec hc').1 hz'
  rw [ex] at b1 b2
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hc0' : (0 : ℤ) ≤ c' := by positivity
  have hcl : (c : ℤ) ≤ 2 := by exact_mod_cast (show c ≤ 2 by omega)
  have hcl' : (c' : ℤ) ≤ 2 := by exact_mod_cast (show c' ≤ 2 by omega)
  have g1 : -(3 * (2 * r + s)) ≤ t * (3 * (2 * r + s)) := by nlinarith
  have g2 : t * (3 * (2 * r + s)) ≤ 3 * (2 * r + s) := by nlinarith
  rcases small_mul hm g1 g2 with rfl | rfl | rfl
  · -- `z` at `3m` in sector 2, `z'` at `0` in sector 0: record 2 from `z`
    have : (c : ℤ) = 2 ∧ (c' : ℤ) = 0 := by constructor <;> nlinarith
    obtain ⟨e1, e2⟩ := this
    have : c = 2 := by exact_mod_cast e1
    have : c' = 0 := by exact_mod_cast e2
    subst c c'
    refine Or.inr ⟨2, by omega, Or.inl ⟨rfl, rfl, ?_⟩⟩
    simp only [recMap, if_neg (show ¬ (2 : ℕ) < 2 by omega), if_pos]
    ext <;> simp [per] <;> ring
  · have e0 : z + (0 : ℤ) • per r s = z := by ext <;> simp [per]
    rw [e0]
    simp only [zero_mul, add_zero] at b1 b2
    -- same point; sectors equal or adjacent
    rcases (show c = c' ∨ c' = c + 1 ∨ c = c' + 1 ∨ (c = 0 ∧ c' = 2) ∨ (c = 2 ∧ c' = 0) by omega)
      with e | e | e | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨by omega, rfl⟩
    · subst e
      refine Or.inr ⟨c, by omega, Or.inl ⟨?_, ?_, ?_⟩⟩
      · unfold rsrc; split_ifs <;> omega
      · unfold rtgt; split_ifs <;> omega
      · simp only [recMap, if_pos (show c < 2 by omega)]
    · subst e
      refine Or.inr ⟨c', by omega, Or.inr ⟨?_, ?_, ?_⟩⟩
      · unfold rsrc; split_ifs <;> omega
      · unfold rtgt; split_ifs <;> omega
      · simp only [recMap, if_pos (show c' < 2 by omega)]
    · subst e1 e2; push_cast at a1 a2 b1 b2; nlinarith
    · subst e1 e2; push_cast at a1 a2 b1 b2; nlinarith
  · have : (c : ℤ) = 0 ∧ (c' : ℤ) = 2 := by constructor <;> nlinarith
    obtain ⟨e1, e2⟩ := this
    have : c = 0 := by exact_mod_cast e1
    have : c' = 2 := by exact_mod_cast e2
    subst c c'
    refine Or.inr ⟨2, by omega, Or.inr ⟨rfl, rfl, ?_⟩⟩
    simp only [recMap, if_neg (show ¬ (2 : ℕ) < 2 by omega), if_pos]
    ext <;> simp [per]

/-- `ch` is injective on one sector. -/
theorem sec_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {f : ℕ} (hf : 2 ≤ f) (hf5 : f < 5) {z z' : ℤ × ℤ}
    (hz : QD p r s f z) (hz' : QD p r s f z') (h : ch p r s w 2 z = ch p r s w 2 z') : z = z' := by
  obtain ⟨t, rfl⟩ := chT_rep hr hs h
  obtain ⟨c, hc, rfl⟩ : ∃ c, c < 3 ∧ f = 2 + c := ⟨f - 2, by omega, by omega⟩
  obtain ⟨a1, a2, -⟩ := (qd_sec hc).1 hz
  obtain ⟨b1, b2, -⟩ := (qd_sec hc).1 hz'
  have ex : (z + t • per r s).1 = z.1 + t * (3 * (2 * r + s)) := by simp [per]
  rw [ex] at b1 b2
  have : t = 0 := by
    rcases (show t ≤ -1 ∨ t = 0 ∨ 1 ≤ t by omega) with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst this; simp

/-- **Placing two columns in one sector.** -/
theorem tube_place (hr : 1 ≤ r) (hs : 1 ≤ s) (x0 : ℤ) :
    ∃ (t : ℤ) (c : ℕ), c < 3 ∧ ∀ z : ℤ × ℤ, HT p z → (z.1 = x0 ∨ z.1 = x0 + 1) →
      QD p r s (2 + c) (z + t • per r s) := by
  have hm : 0 < 2 * r + s := by omega
  obtain ⟨q, b, hq, hb0, hb1⟩ : ∃ q b, x0 = 3 * (2 * r + s) * q + b ∧ 0 ≤ b ∧ b < 3 * (2 * r + s) :=
    ⟨x0 / (3 * (2 * r + s)), x0 % (3 * (2 * r + s)), (Int.mul_ediv_add_emod _ _).symm,
      Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hx : ∀ z : ℤ × ℤ, (z + (-q) • per r s).1 = z.1 - 3 * (2 * r + s) * q := by
    intro z; simp [per]; ring
  have hT : ∀ z : ℤ × ℤ, HT p z → HT p (z + (-q) • per r s) := fun z h => HT_shift _ h
  rcases (show b < 2 * r + s ∨ (2 * r + s ≤ b ∧ b < 2 * (2 * r + s)) ∨
      2 * (2 * r + s) ≤ b by omega) with h | h | h
  · refine ⟨-q, 0, by omega, fun z hz hz1 => (qd_sec (by omega)).2 ⟨?_, ?_, hT z hz⟩⟩ <;>
      rw [hx] <;> push_cast <;> omega
  · refine ⟨-q, 1, by omega, fun z hz hz1 => (qd_sec (by omega)).2 ⟨?_, ?_, hT z hz⟩⟩ <;>
      rw [hx] <;> push_cast <;> omega
  · refine ⟨-q, 2, by omega, fun z hz hz1 => (qd_sec (by omega)).2 ⟨?_, ?_, hT z hz⟩⟩ <;>
      rw [hx] <;> push_cast <;> omega

end Claude5E10
