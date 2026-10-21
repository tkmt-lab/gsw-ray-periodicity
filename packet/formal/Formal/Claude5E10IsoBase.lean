import Formal.Claude5E10Deg4

/-!
# E10: the spec surface and the tube model — the general transfer

Written by a Claude worker (2026-10-20, E10 bridge session).

* `Phi f z` : the model vertex of the point `z` of cell `f` (cells 0, 1: the caps, the chart
  points themselves; cell `2 + c`: the tube chart point `z + (c m, −c m)`);
* `cpt v`   : a canonical cell point of a model vertex (`cpt_phi`: its image is `v`);
* `IsoOK`   : what is checked case by case (cells = domains, gluings preserve `Phi`, every
  site is glued to the canonical site of its image);
* `iso_of`  : `IsoOK` gives `PathExists p r s ↔ ∃ literal path in the model`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- A tube sector in its cell coordinates. -/
def SD (p r s : ℤ) (z : ℤ × ℤ) : Prop :=
  0 ≤ z.1 ∧ z.1 ≤ 2 * r + s ∧ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 2 * p

/-- The cell domains. -/
def CD (p r s : ℤ) (f : Fin 5) (z : ℤ × ℤ) : Prop :=
  if f.val = 0 then HL r s z else if f.val = 1 then HU r s z else SD p r s z

/-- The offset of a sector. -/
def soff (r s : ℤ) (f : Fin 5) : ℤ × ℤ := (((f.val : ℤ) - 2) * (2 * r + s), -(((f.val : ℤ) - 2) * (2 * r + s)))

/-- The model vertex of a cell point. -/
def Phi (p r s w : ℤ) (f : Fin 5) (z : ℤ × ℤ) : MV :=
  if f.val = 0 then ch p r s w 0 z else if f.val = 1 then ch p r s w 1 z
  else ch p r s w 2 (z + soff r s f)

/-- The canonical cell point of a model vertex. -/
def cpt (r s : ℤ) (v : MV) : Fin 5 × (ℤ × ℤ) :=
  if v.1 = 0 then (0, v.2) else if v.1 = 1 then (1, v.2)
  else if v.2.1 < 2 * r + s then (2, (v.2.1, v.2.2 - v.2.1))
  else if v.2.1 < 2 * (2 * r + s) then (3, (v.2.1 - (2 * r + s), v.2.2 - v.2.1 + (2 * r + s)))
  else (4, (v.2.1 - 2 * (2 * r + s), v.2.2 - v.2.1 + 2 * (2 * r + s)))

theorem cpt_T (u h : ℤ) : cpt r s (2, (u, h)) =
    if u < 2 * r + s then (2, (u, h - u))
    else if u < 2 * (2 * r + s) then (3, (u - (2 * r + s), h - u + (2 * r + s)))
    else (4, (u - 2 * (2 * r + s), h - u + 2 * (2 * r + s))) := by
  simp [cpt]

theorem cpt_dom (H : Hyp p r s w) {v : MV} (hv : Valid p r s v) : CD p r s (cpt r s v).1 (cpt r s v).2 := by
  obtain ⟨k, u, h⟩ := v
  rcases hv with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h0, h1, h2, h3⟩ <;> simp only at hk <;> subst hk
  · show HL r s (u, h); simp only [IL, HL] at hz ⊢; omega
  · show HU r s (u, h); simp only [IU, HU] at hz ⊢; omega
  · simp only at h0 h1 h2 h3
    rw [cpt_T]
    split_ifs
    · show SD p r s _; simp only [SD]; omega
    · show SD p r s _; simp only [SD]; omega
    · show SD p r s _; simp only [SD]; omega

theorem cpt_phi (H : Hyp p r s w) {v : MV} (hv : Valid p r s v) :
    Phi p r s w (cpt r s v).1 (cpt r s v).2 = v := by
  obtain ⟨k, u, h⟩ := v
  have hP : 0 < 3 * (2 * r + s) := by have := H.hr; have := H.hs; omega
  rcases hv with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h0, h1, h2, h3⟩ <;> simp only at hk <;> subst hk
  · show ch p r s w 0 (u, h) = _; exact chL_I hz
  · show ch p r s w 1 (u, h) = _; exact chU_I hz
  · simp only at h0 h1 h2 h3
    rw [cpt_T]
    have fin : ch p r s w 2 (u, h - u) = (2, (u, h)) := by
      rw [chT]; simp only [Prod.mk.injEq, true_and]; exact ⟨Int.emod_eq_of_lt h0 h1, by ring⟩
    split_ifs
    · show ch p r s w 2 ((u, h - u) + soff r s 2) = _
      rw [show (u, h - u) + soff r s 2 = (u, h - u) by ext <;> simp [soff], fin]
    · show ch p r s w 2 ((u - (2 * r + s), h - u + (2 * r + s)) + soff r s 3) = _
      rw [show (u - (2 * r + s), h - u + (2 * r + s)) + soff r s 3 = (u, h - u) by
        ext <;> simp [soff] <;> ring, fin]
    · show ch p r s w 2 ((u - 2 * (2 * r + s), h - u + 2 * (2 * r + s)) + soff r s 4) = _
      rw [show (u - 2 * (2 * r + s), h - u + 2 * (2 * r + s)) + soff r s 4 = (u, h - u) by
        ext <;> simp [soff] <;> ring, fin]

/-- What is checked for each combinatorial case. -/
structure IsoOK (p r s w : ℤ) : Prop where
  incell : ∀ f z, (e10Sig p r s).InCell f z ↔ CD p r s f z
  same : ∀ a b : (e10Sig p r s).Site, (e10Sig p r s).SamePoint a b →
    Phi p r s w a.1.1 a.1.2 = Phi p r s w b.1.1 b.1.2
  canon : ∀ a : (e10Sig p r s).Site, ∀ h : (e10Sig p r s).InCell (cpt r s (Phi p r s w a.1.1 a.1.2)).1
    (cpt r s (Phi p r s w a.1.1 a.1.2)).2,
    Relation.EqvGen (e10Sig p r s).SamePoint a ⟨cpt r s (Phi p r s w a.1.1 a.1.2), h⟩

end Claude5E10
